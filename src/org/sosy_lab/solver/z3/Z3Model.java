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

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_value;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_get_entry;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_get_num_entries;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_arity;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_eval;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_func_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_func_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_num_consts;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_num_funcs;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_to_string;

import com.google.common.base.Preconditions;
import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.UnmodifiableIterator;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final long z3context;
  private final Z3FormulaCreator creator;

  Z3Model(long z3context, long z3model, Z3FormulaCreator pCreator) {
    super(pCreator);
    model_inc_ref(z3context, z3model);
    model = z3model;
    this.z3context = z3context;
    creator = pCreator;
  }

  @Nullable
  @Override
  public Object evaluateImpl(Long f) {
    PointerToLong out = new PointerToLong();
    boolean status = model_eval(z3context, model, f, true, out);
    Verify.verify(status, "Error during model evaluation");
    if (out.value == 0) {
      return null;
    }
    return creator.convertValue(out.value);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return new Z3ModelIterator();
  }

  private class Z3ModelIterator extends UnmodifiableIterator<ValueAssignment> {
    final int numConsts;
    final int numFuncs;

    int constCursor = -1;
    int funcCursor = -1;
    int funcArgCursor = -1;

    Z3ModelIterator() {
      numConsts = model_get_num_consts(z3context, model);
      numFuncs = model_get_num_funcs(z3context, model);
    }

    @Override
    public boolean hasNext() {

      // Advance cursor first.
      if (constCursor + 1 < numConsts) {

        // Simplest case, next application is a constant.
        constCursor++;
        return true;
      } else if (funcCursor + 1 < numFuncs) {

        int numInterpretations = getNumInterpretations();
        if (funcArgCursor + 1 < numInterpretations) {

          // More interpretations left.
          funcArgCursor++;
          return true;
        } else {

          funcCursor++;
          funcArgCursor = 0;

          // Function with no interpretations makes this case complicated.
          return funcArgCursor >= getNumInterpretations() || hasNext();
        }
      } else {
        return false;
      }
    }

    @Override
    public ValueAssignment next() {
      if (constCursor != numConsts) {
        return nextConstant();
      } else {
        return nextFuncApp();
      }
    }

    int getNumInterpretations() {
      long funcDecl = model_get_func_decl(z3context, model, funcCursor);
      inc_ref(z3context, funcDecl);
      long interp = model_get_func_interp(z3context, model, funcDecl);
      func_interp_inc_ref(z3context, interp);
      int numInterpretations = func_interp_get_num_entries(z3context, interp);
      dec_ref(z3context, funcDecl);
      func_interp_dec_ref(z3context, interp);
      return numInterpretations;
    }

    ValueAssignment nextConstant() {
      long keyDecl = model_get_const_decl(z3context, model, constCursor);
      inc_ref(z3context, keyDecl);

      Preconditions.checkArgument(
          get_arity(z3context, keyDecl) == 0, "Declaration is not a constant");

      long var = mk_app(z3context, keyDecl);
      Formula key = creator.encapsulateWithTypeOf(var);

      long value = model_get_const_interp(z3context, model, keyDecl);
      inc_ref(z3context, value);

      long symbol = get_decl_name(z3context, keyDecl);
      assert get_symbol_kind(z3context, symbol) == Z3NativeApiConstants.Z3_STRING_SYMBOL;
      String name = get_symbol_string(z3context, symbol);
      Object lValue = creator.convertValue(value);

      // cleanup outdated data
      dec_ref(z3context, keyDecl);
      dec_ref(z3context, value);

      return new ValueAssignment(key, name, lValue, ImmutableList.of());
    }

    ValueAssignment nextFuncApp() {
      long funcDecl = model_get_func_decl(z3context, model, funcCursor);
      inc_ref(z3context, funcDecl);

      long symbol = get_decl_name(z3context, funcDecl);
      assert get_symbol_kind(z3context, symbol) == Z3NativeApiConstants.Z3_STRING_SYMBOL;
      String name = get_symbol_string(z3context, symbol);

      long interp = model_get_func_interp(z3context, model, funcDecl);
      func_interp_inc_ref(z3context, interp);

      int numInterpretations = getNumInterpretations();
      long entry = func_interp_get_entry(z3context, interp, funcArgCursor);

      func_entry_inc_ref(z3context, entry);

      Object value = creator.convertValue(func_entry_get_value(z3context, entry));

      int noArgs = func_entry_get_num_args(z3context, entry);
      long[] args = new long[noArgs];

      List<Object> argumentInterpretation = new ArrayList<>();

      for (int i = 0; i < noArgs; i++) {
        long arg = func_entry_get_arg(z3context, entry, i);
        inc_ref(z3context, arg);
        argumentInterpretation.add(evaluateImpl(arg));
        args[i] = arg;
      }

      Formula formula = creator.encapsulateWithTypeOf(mk_app(z3context, funcDecl, args));

      // Clean up memory.
      for (long arg : args) {
        dec_ref(z3context, arg);
      }
      func_entry_dec_ref(z3context, entry);
      func_interp_dec_ref(z3context, interp);
      dec_ref(z3context, funcDecl);

      return new ValueAssignment(formula, name, value, argumentInterpretation);
    }
  }

  @Override
  public String toString() {
    return model_to_string(z3context, model);
  }

  /** Delays the conversion to string. */
  private static class LazyString {

    final long value;
    final long z3context;

    LazyString(long v, long pZ3context) {
      value = v;
      z3context = pZ3context;
    }

    @Override
    public String toString() {
      return ast_to_string(z3context, value); // this could be an expensive operation!
    }
  }
}
