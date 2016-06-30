/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.z3;

import com.google.common.base.Preconditions;
import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;
import com.microsoft.z3.Native;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final long z3context;

  @SuppressWarnings("hiding")
  private final Z3FormulaCreator creator;

  private @Nullable ImmutableList<ValueAssignment> assignments = null;

  private Z3Model(long z3context, long z3model, Z3FormulaCreator pCreator) {
    super(pCreator);
    Native.modelIncRef(z3context, z3model);
    model = z3model;
    this.z3context = z3context;
    creator = pCreator;
  }

  static Z3Model create(long z3context, long z3model, Z3FormulaCreator pCreator) {
    return new Z3Model(z3context, z3model, pCreator);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Long f) {
    Native.LongPtr out = new Native.LongPtr();
    boolean status = Native.modelEval(z3context, model, f, false, out);
    Verify.verify(status, "Error during model evaluation");
    long outValue = out.value;

    if (creator.isConstant(outValue)) {
      return creator.convertValue(outValue);
    }
    return null;
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    if (assignments == null) {

      // Cache model values.
      assignments = modelToList();
    }
    return assignments.iterator();
  }

  ImmutableList<ValueAssignment> modelToList() {
    Builder<ValueAssignment> out = ImmutableList.builder();

    // Iterate through constants.
    for (int constIdx = 0; constIdx < Native.modelGetNumConsts(z3context, model); constIdx++) {
      long keyDecl = Native.modelGetConstDecl(z3context, model, constIdx);
      Native.incRef(z3context, keyDecl);
      out.add(getConstAssignment(keyDecl));
      Native.decRef(z3context, keyDecl);
    }

    // Iterate through function applications.
    for (int funcIdx = 0; funcIdx < Native.modelGetNumFuncs(z3context, model); funcIdx++) {
      long funcDecl = Native.modelGetFuncDecl(z3context, model, funcIdx);
      Native.incRef(z3context, funcDecl);
      String functionName = creator.symbolToString(Native.getDeclName(z3context, funcDecl));
      out.addAll(getFunctionAssignments(funcDecl, funcDecl, functionName));
      Native.decRef(z3context, funcDecl);
    }

    return out.build();
  }

  /** get a ValueAssignment for a constant declaration in the model */
  private ValueAssignment getConstAssignment(long keyDecl) {
    Preconditions.checkArgument(
        Native.getArity(z3context, keyDecl) == 0, "Declaration is not a constant");

    long var = Native.mkApp(z3context, keyDecl, 0, new long[] {});
    Formula key = creator.encapsulateWithTypeOf(var);

    long value = Native.modelGetConstInterp(z3context, model, keyDecl);
    Native.incRef(z3context, value);

    long symbol = Native.getDeclName(z3context, keyDecl);
    final Object lValue;
    if (creator.isConstant(value)) {
      lValue = creator.convertValue(value);

    } else if (Native.isAsArray(z3context, value)) {
      lValue = getArrayAssignment(symbol, value);

    } else {
      throw new AssertionError("unexpected value: " + Native.astToString(z3context, value));
    }

    // cleanup outdated data
    Native.decRef(z3context, value);

    return new ValueAssignment(key, creator.symbolToString(symbol), lValue, ImmutableList.of());
  }

  /** Z3 models an array as uninterpreted function.
   * We try to produce a proper array representation.
   * There are several possibilities to model an array in Java-SMT:
   * <ul>
   * <li> as direct array like "[0,0,?,?,0]" (not useful, if many cells are empty or unused)
   * <li> as map like "{1:0, 2:0, 5:0}" (human-readable)
   * <li> as array formula like "(store (store (store arrSymbol 1 0) 2 0) 5 0)"
   *  (based on formulas, our choice)
   * </ul>
   */
  private Formula getArrayAssignment(long arraySymbol, long value) {
    long evalDecl = Native.getAsArrayFuncDecl(z3context, value);
    Native.incRef(z3context, evalDecl);
    long interp = Native.modelGetFuncInterp(z3context, model, evalDecl);
    Native.funcInterpIncRef(z3context, interp);

    long array = Native.mkConst(z3context, arraySymbol, Native.getSort(z3context, value));
    Native.incRef(z3context, array);

    // get all assignments for the array
    int numInterpretations = Native.funcInterpGetNumEntries(z3context, interp);
    for (int interpIdx = 0; interpIdx < numInterpretations; interpIdx++) {
      long entry = Native.funcInterpGetEntry(z3context, interp, interpIdx);
      Native.funcEntryIncRef(z3context, entry);
      long newArray = storeAssignment(array, entry);
      Native.decRef(z3context, array);
      Native.funcEntryDecRef(z3context, entry);
      array = newArray;
    }

    Native.funcInterpDecRef(z3context, interp);
    Native.decRef(z3context, evalDecl);
    return creator.encapsulateWithTypeOf(array);
  }

  /** returns a new array formula "(store array index value)".
   *
   * @param array the basic array
   * @param entry where index and value are extracted from */
  private long storeAssignment(long array, long entry) {
    long arrayValue = Native.funcEntryGetValue(z3context, entry);
    Native.incRef(z3context, arrayValue);
    int noArgs = Native.funcEntryGetNumArgs(z3context, entry);
    assert noArgs == 1 : "array modelled as UF is expected to have only one parameter, aka index";
    long arrayIndex = Native.funcEntryGetArg(z3context, entry, 0);
    Native.incRef(z3context, arrayIndex);

    long newArray = Native.mkStore(z3context, array, arrayIndex, arrayValue);
    Native.incRef(z3context, newArray);
    return newArray;
  }

  /**
   * get all ValueAssignments for a function declaration in the model
   *
   * @param evalDecl function declaration where the evaluation comes from
   * @param funcDecl function declaration where the function name comes from
   * @param functionName the name of the funcDecl
   */
  private Collection<ValueAssignment> getFunctionAssignments(
      long evalDecl, long funcDecl, String functionName) {
    long interp = Native.modelGetFuncInterp(z3context, model, evalDecl);
    Native.funcInterpIncRef(z3context, interp);

    List<ValueAssignment> lst = new ArrayList<>();

    int numInterpretations = Native.funcInterpGetNumEntries(z3context, interp);

    if (numInterpretations == 0) {
      // we found an alias in the model, follow the alias
      long elseInterp = Native.funcInterpGetElse(z3context, interp);
      Native.incRef(z3context, elseInterp);
      long aliasDecl = Native.getAppDecl(z3context, elseInterp);
      Native.incRef(z3context, aliasDecl);
      if (creator.symbolToString(Native.getDeclName(z3context, aliasDecl)).contains("!")) {
        // The symbol "!" is part of temporary symbols used for quantified formulas.
        // This is only a heuristic, because the user can also create a symbol containing "!".
        lst.addAll(getFunctionAssignments(aliasDecl, funcDecl, functionName));
        // TODO Can we guarantee termination of this recursive call?
        //      A chain of aliases should end after several steps.
      } else {
        // ignore functionDeclarations like "ite", "and",...
      }
      Native.decRef(z3context, aliasDecl);
      Native.decRef(z3context, elseInterp);

    } else {
      for (int interpIdx = 0; interpIdx < numInterpretations; interpIdx++) {
        long entry = Native.funcInterpGetEntry(z3context, interp, interpIdx);
        Native.funcEntryIncRef(z3context, entry);
        lst.add(getFunctionAssignment(functionName, funcDecl, entry));
        Native.funcEntryDecRef(z3context, entry);
      }
    }

    Native.funcInterpDecRef(z3context, interp);
    return lst;
  }

  /** get a ValueAssignment for an entry (= one evaluation)
   * of an uninterpreted function in the model */
  private ValueAssignment getFunctionAssignment(String functionName, long funcDecl, long entry) {
    Object value = creator.convertValue(Native.funcEntryGetValue(z3context, entry));
    int noArgs = Native.funcEntryGetNumArgs(z3context, entry);
    long[] args = new long[noArgs];
    List<Object> argumentInterpretation = new ArrayList<>();

    for (int k = 0; k < noArgs; k++) {
      long arg = Native.funcEntryGetArg(z3context, entry, k);
      Native.incRef(z3context, arg);
      argumentInterpretation.add(creator.convertValue(arg));
      args[k] = arg;
    }
    Formula formula =
        creator.encapsulateWithTypeOf(Native.mkApp(z3context, funcDecl, args.length, args));

    // Clean up memory.
    for (long arg : args) {
      Native.decRef(z3context, arg);
    }

    return new ValueAssignment(formula, functionName, value, argumentInterpretation);
  }

  @Override
  public void close() {
    Native.modelDecRef(z3context, model);
  }
}
