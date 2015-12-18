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
package org.sosy_lab.solver.basicimpl;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.UnsafeFormulaManager;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv> implements UnsafeFormulaManager {

  protected AbstractUnsafeFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv> creator) {
    super(creator);
  }

  private <T extends Formula> T encapsulateWithTypeOf(T f, TFormulaInfo e) {
    FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator = getFormulaCreator();
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), e);
  }

  @Override
  @Deprecated
  public boolean isAtom(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isAtom(t);
  }

  protected abstract boolean isAtom(TFormulaInfo pT);

  @Override
  public int getArity(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return getArity(t);
  }

  protected abstract int getArity(TFormulaInfo pT);

  @Override
  public Formula getArg(Formula pF, int pN) {
    assert 0 <= pN && pN < getArity(pF)
        : String.format("index %d out of bounds %d", pN, getArity(pF));
    TFormulaInfo t = extractInfo(pF);
    TFormulaInfo arg = getArg(t, pN);
    FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator = getFormulaCreator();
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(arg), arg);
  }

  protected abstract TFormulaInfo getArg(TFormulaInfo pT, int n);

  @Override
  public List<Formula> getAllArgs(Formula pF) {
    int arity = getArity(pF);
    List<Formula> args = new ArrayList<>(arity);
    for (int i = 0; i < arity; i++) {
      args.add(getArg(pF, i));
    }
    return args;
  }

  @Override
  public boolean isVariable(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isVariable(t);
  }

  protected abstract boolean isVariable(TFormulaInfo pT);

  @Override
  public boolean isFreeVariable(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isFreeVariable(t);
  }

  protected abstract boolean isFreeVariable(TFormulaInfo pT);

  @Override
  public boolean isBoundVariable(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isBoundVariable(t);
  }

  protected abstract boolean isBoundVariable(TFormulaInfo pT);

  @Override
  @Deprecated
  public boolean isQuantification(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isQuantification(t);
  }

  protected abstract boolean isQuantification(TFormulaInfo pT);

  @Override
  @Deprecated
  public BooleanFormula getQuantifiedBody(Formula pQuantifiedFormula) {
    Preconditions.checkArgument(isQuantification(pQuantifiedFormula));

    TFormulaInfo t = extractInfo(pQuantifiedFormula);
    TFormulaInfo result = getQuantifiedBody(t);

    return getFormulaCreator().encapsulateBoolean(result);
  }

  protected abstract TFormulaInfo getQuantifiedBody(TFormulaInfo pT);

  @Override
  public boolean isNumber(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isNumber(t);
  }

  @Override
  public BooleanFormula replaceQuantifiedBody(BooleanFormula pF, BooleanFormula pNewBody) {
    Preconditions.checkArgument(isQuantification(pF));

    TFormulaInfo f = extractInfo(pF);
    TFormulaInfo body = extractInfo(pNewBody);
    TFormulaInfo result = replaceQuantifiedBody(f, body);

    return getFormulaCreator().encapsulateBoolean(result);
  }

  protected abstract TFormulaInfo replaceQuantifiedBody(TFormulaInfo pF, TFormulaInfo pBody);

  protected abstract boolean isNumber(TFormulaInfo pT);

  @Override
  public boolean isUF(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return isUF(t);
  }

  protected abstract boolean isUF(TFormulaInfo pT);

  @Override
  public String getName(Formula pF) {

    TFormulaInfo t = extractInfo(pF);
    return getName(t);
  }

  protected abstract String getName(TFormulaInfo pT);

  @Override
  public <T extends Formula> T replaceArgsAndName(T f, String newName, List<Formula> args) {
    return encapsulateWithTypeOf(
        f, replaceArgsAndName(extractInfo(f), newName, Lists.transform(args, extractor)));
  }

  protected abstract TFormulaInfo replaceArgsAndName(
      TFormulaInfo pT, String newName, List<TFormulaInfo> newArgs);

  @Override
  public <T extends Formula> T replaceArgs(T pF, List<Formula> pArgs) {
    assert pArgs.size() == getArity(pF) : "number of args must match arity.";
    return encapsulateWithTypeOf(
        pF, replaceArgs(extractInfo(pF), Lists.transform(pArgs, extractor)));
  }

  protected abstract TFormulaInfo replaceArgs(TFormulaInfo pT, List<TFormulaInfo> newArgs);

  @Override
  public <T extends Formula> List<T> splitNumeralEqualityIfPossible(final T pF) {
    return Lists.transform(
        splitNumeralEqualityIfPossible(extractInfo(pF)),
        new Function<TFormulaInfo, T>() {
          @Override
          public T apply(TFormulaInfo input) {
            return encapsulateWithTypeOf(pF, input);
          }
        });
  }

  protected abstract List<? extends TFormulaInfo> splitNumeralEqualityIfPossible(TFormulaInfo pF);

  /**
   * Default implementation for {@link #substitute(Formula, Map)}.
   */
  protected final <T1 extends Formula, T2 extends Formula> T1 substituteUsingMap(
      T1 pF, Map<T2, T2> pFromToMapping) {
    Map<TFormulaInfo, TFormulaInfo> mapping = new HashMap<>(pFromToMapping.size());
    for (Map.Entry<T2, T2> entry : pFromToMapping.entrySet()) {
      mapping.put(extractInfo(entry.getKey()), extractInfo(entry.getValue()));
    }

    TFormulaInfo result = substituteUsingMapImpl(extractInfo(pF), mapping);
    FormulaType<T1> type = getFormulaCreator().getFormulaType(pF);
    return getFormulaCreator().encapsulate(type, result);
  }

  protected TFormulaInfo substituteUsingMapImpl(
      TFormulaInfo expr, Map<TFormulaInfo, TFormulaInfo> memoization) {
    TFormulaInfo out = memoization.get(expr);

    if (out == null) {
      int arity = getArity(expr);
      List<TFormulaInfo> updatedChildren = new ArrayList<>(arity);
      for (int childIdx = 0; childIdx < arity; childIdx++) {
        TFormulaInfo child = getArg(expr, childIdx);
        updatedChildren.add(substituteUsingMapImpl(child, memoization));
      }
      out = replaceArgs(expr, updatedChildren);
      memoization.put(expr, out);
    }

    return out;
  }

  /**
   * Default implementation for {@link #substitute(Formula, Map)} for solvers that provide
   * an internal substitute operation that takes two lists instead of a map.
   *
   * <p>If this is called, one needs to overwrite {@link #substituteUsingLists(Formula, Map)}.
   */
  protected final <T1 extends Formula, T2 extends Formula> T1 substituteUsingLists(
      T1 pF, Map<T2, T2> pFromToMapping) {
    List<TFormulaInfo> substituteFrom = new ArrayList<>(pFromToMapping.size());
    List<TFormulaInfo> substituteTo = new ArrayList<>(pFromToMapping.size());
    for (Map.Entry<T2, T2> entry : pFromToMapping.entrySet()) {
      substituteFrom.add(extractInfo(entry.getKey()));
      substituteTo.add(extractInfo(entry.getValue()));
    }

    TFormulaInfo result = substituteUsingListsImpl(extractInfo(pF), substituteFrom, substituteTo);
    FormulaType<T1> type = getFormulaCreator().getFormulaType(pF);
    return getFormulaCreator().encapsulate(type, result);
  }

  /**
   * Backend for {@link #substituteUsingLists(Formula, Map)}.
   * @param pF The formula to change.
   * @param substituteFrom The list of parts that should be replaced.
   * @param substituteTo The list of replacement parts, in same order.
   * @return The formula with th replacements applied.
   */
  protected TFormulaInfo substituteUsingListsImpl(
      TFormulaInfo pF, List<TFormulaInfo> substituteFrom, List<TFormulaInfo> substituteTo) {
    throw new UnsupportedOperationException();
  }
}
