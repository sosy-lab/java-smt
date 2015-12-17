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

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.Collections2;
import com.google.common.collect.Iterables;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public abstract class AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv> implements BooleanFormulaManager {

  private final AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv> ufmgr;

  protected AbstractBooleanFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv> pCreator,
      AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv> ufmgr) {
    super(pCreator);
    this.ufmgr = ufmgr;
  }

  @Override
  public boolean isBoolean(Formula f) {
    return f instanceof BooleanFormula;
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    return wrap(makeVariableImpl(pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public BooleanFormula makeBoolean(boolean value) {
    return wrap(makeBooleanImpl(value));
  }

  protected abstract TFormulaInfo makeBooleanImpl(boolean value);

  @Override
  public BooleanFormula not(BooleanFormula pBits) {
    TFormulaInfo param1 = extractInfo(pBits);
    return wrap(not(param1));
  }

  protected abstract TFormulaInfo not(TFormulaInfo pParam1);

  @Override
  public BooleanFormula and(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(and(param1, param2));
  }

  protected abstract TFormulaInfo and(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula and(Collection<BooleanFormula> pBits) {
    if (pBits.isEmpty()) {
      return makeBoolean(true);
    }
    if (pBits.size() == 1) {
      return Iterables.getOnlyElement(pBits);
    }
    TFormulaInfo result = andImpl(Collections2.transform(pBits, extractor));
    return wrap(result);
  }

  protected TFormulaInfo andImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(true);
    for (TFormulaInfo formula : pParams) {
      result = and(result, formula);
    }
    return result;
  }

  @Override
  public BooleanFormula or(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(or(param1, param2));
  }

  protected abstract TFormulaInfo or(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula xor(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(xor(param1, param2));
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> pBits) {
    if (pBits.isEmpty()) {
      return makeBoolean(false);
    }
    if (pBits.size() == 1) {
      return Iterables.getOnlyElement(pBits);
    }
    TFormulaInfo result = orImpl(Collections2.transform(pBits, extractor));
    return wrap(result);
  }

  protected TFormulaInfo orImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(false);
    for (TFormulaInfo formula : pParams) {
      result = or(result, formula);
    }
    return result;
  }

  protected abstract TFormulaInfo xor(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  @Deprecated
  public boolean isNot(BooleanFormula pBits) {
    TFormulaInfo param = extractInfo(pBits);
    return isNot(param);
  }

  protected abstract boolean isNot(TFormulaInfo pParam);

  @Override
  @Deprecated
  public boolean isAnd(BooleanFormula pBits) {
    TFormulaInfo param = extractInfo(pBits);
    return isAnd(param);
  }

  protected abstract boolean isAnd(TFormulaInfo pParam);

  @Override
  @Deprecated
  public boolean isOr(BooleanFormula pBits) {
    TFormulaInfo param = extractInfo(pBits);
    return isOr(param);
  }

  protected abstract boolean isOr(TFormulaInfo pParam);

  @Override
  @Deprecated
  public boolean isXor(BooleanFormula pBits) {
    TFormulaInfo param = extractInfo(pBits);
    return isXor(param);
  }

  protected abstract boolean isXor(TFormulaInfo pParam);

  /**
   * Creates a formula representing an equivalence of the two arguments.
   * @param pBits1 a Formula
   * @param pBits2 a Formula
   * @return {@code f1 <-> f2}
   */
  @Override
  public final BooleanFormula equivalence(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(equivalence(param1, param2));
  }

  protected abstract TFormulaInfo equivalence(TFormulaInfo bits1, TFormulaInfo bits2);

  @Override
  public final BooleanFormula implication(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(implication(param1, param2));
  }

  protected TFormulaInfo implication(TFormulaInfo bits1, TFormulaInfo bits2) {
    return or(not(bits1), bits2);
  }

  @Override
  public final boolean isTrue(BooleanFormula pBits) {
    return isTrue(extractInfo(pBits));
  }

  protected abstract boolean isTrue(TFormulaInfo bits);

  @Override
  public final boolean isFalse(BooleanFormula pBits) {
    return isFalse(extractInfo(pBits));
  }

  protected abstract boolean isFalse(TFormulaInfo bits);

  /**
   * Creates a formula representing "IF cond THEN f1 ELSE f2"
   * @param pBits a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  @Override
  public final <T extends Formula> T ifThenElse(BooleanFormula pBits, T f1, T f2) {
    FormulaType<T> t1 = getFormulaCreator().getFormulaType(f1);
    FormulaType<T> t2 = getFormulaCreator().getFormulaType(f2);
    checkArgument(
        t1.equals(t2),
        "Cannot create if-then-else formula with branches of different types: "
            + "%s is of type %s; %s is of type %s",
        f1,
        t1,
        f2,
        t2);
    TFormulaInfo result = ifThenElse(extractInfo(pBits), extractInfo(f1), extractInfo(f2));
    return getFormulaCreator().encapsulate(t1, result);
  }

  protected abstract TFormulaInfo ifThenElse(TFormulaInfo cond, TFormulaInfo f1, TFormulaInfo f2);

  @Override
  @Deprecated
  public boolean isEquivalence(BooleanFormula pFormula) {
    return isEquivalence(extractInfo(pFormula));
  }

  protected abstract boolean isEquivalence(TFormulaInfo pBits);

  @Override
  @Deprecated
  public boolean isImplication(BooleanFormula pFormula) {
    return isImplication(extractInfo(pFormula));
  }

  protected abstract boolean isImplication(TFormulaInfo pFormula);

  @Override
  @Deprecated
  public <T extends Formula> boolean isIfThenElse(T pF) {
    return isIfThenElse(extractInfo(pF));
  }

  protected abstract boolean isIfThenElse(TFormulaInfo pBits);

  @Override
  public <R> R visit(BooleanFormulaVisitor<R> visitor, BooleanFormula pFormula) {
    return visit(visitor, extractInfo(pFormula));
  }

  protected abstract <R> R visit(BooleanFormulaVisitor<R> visitor, TFormulaInfo pFormula);

  /**
   * Syntax sugar for type casting.
   */
  protected final BooleanFormula getArg(TFormulaInfo pF, int index) {
    return getFormulaCreator().encapsulateBoolean(ufmgr.getArg(pF, index));
  }

  protected final List<BooleanFormula> getAllArgs(TFormulaInfo pF) {
    return checkedCast(ufmgr.getAllArgs(getFormulaCreator().encapsulateBoolean(pF)));
  }

  private static List<BooleanFormula> checkedCast(List<Formula> list) {
    List<BooleanFormula> ret = new ArrayList<>(list.size());
    for (Formula f : list) {
      if (f instanceof BooleanFormula) {
        ret.add((BooleanFormula) f);
      } else {
        throw new IllegalStateException(
            "Non-boolean formula where only boolean formulas should occur");
      }
    }
    return ret;
  }
}
