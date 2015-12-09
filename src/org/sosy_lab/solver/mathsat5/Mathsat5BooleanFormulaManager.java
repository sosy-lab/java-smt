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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_bool_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_and;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_iff;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_not;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_or;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_term_ite;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_true;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_and;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_atom;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_iff;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_not;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_or;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_term_ite;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_true;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.List;

class Mathsat5BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long> {

  private final long mathsatEnv;

  protected Mathsat5BooleanFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  public static Mathsat5BooleanFormulaManager create(Mathsat5FormulaCreator creator) {
    return new Mathsat5BooleanFormulaManager(creator);
  }

  @Override
  public Long makeVariableImpl(String pVar) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  public Long makeBooleanImpl(boolean pValue) {
    long v;
    if (pValue) {
      v = msat_make_true(mathsatEnv);
    } else {
      v = msat_make_false(mathsatEnv);
    }

    return v;
  }

  @Override
  public Long equivalence(Long f1, Long f2) {
    return msat_make_iff(mathsatEnv, f1, f2);
  }

  @Override
  public boolean isTrue(Long t) {
    return msat_term_is_true(mathsatEnv, t);
  }

  @Override
  public boolean isFalse(Long t) {
    return msat_term_is_false(mathsatEnv, t);
  }

  @Override
  public Long ifThenElse(Long cond, Long f1, Long f2) {
    long t;
    long msatEnv = mathsatEnv;
    long f1Type = msat_term_get_type(f1);
    long f2Type = msat_term_get_type(f2);

    // ite currently doesn't work with bool-types as branch arguments
    if (!msat_is_bool_type(msatEnv, f1Type) || !msat_is_bool_type(msatEnv, f2Type)) {
      t = msat_make_term_ite(msatEnv, cond, f1, f2);
    } else {
      t =
          msat_make_and(
              msatEnv,
              msat_make_or(msatEnv, msat_make_not(msatEnv, cond), f1),
              msat_make_or(msatEnv, cond, f2));
    }
    return t;
  }

  @Override
  public Long not(Long pBits) {
    return msat_make_not(mathsatEnv, pBits);
  }

  @Override
  public Long and(Long pBits1, Long pBits2) {
    return msat_make_and(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long or(Long pBits1, Long pBits2) {
    return msat_make_or(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long xor(Long pBits1, Long pBits2) {
    return not(msat_make_iff(mathsatEnv, pBits1, pBits2));
  }

  @Override
  public boolean isNot(Long pBits) {
    return msat_term_is_not(mathsatEnv, pBits);
  }

  @Override
  public boolean isAnd(Long pBits) {
    return msat_term_is_and(mathsatEnv, pBits);
  }

  @Override
  public boolean isOr(Long pBits) {
    return msat_term_is_or(mathsatEnv, pBits);
  }

  @Override
  public boolean isXor(Long pBits) {
    boolean isNot = msat_term_is_not(mathsatEnv, pBits);
    if (!isNot) {
      return false;
    }
    long notArg = msat_term_get_arg(pBits, 0);
    return msat_term_is_iff(mathsatEnv, notArg);
  }

  @Override
  public boolean isEquivalence(Long pBits) {
    return msat_term_is_iff(mathsatEnv, pBits);
  }

  @Override
  protected boolean isImplication(Long pFormula) {
    return false; // Mathsat does not have implications
  }

  @Override
  public boolean isIfThenElse(Long pBits) {
    return msat_term_is_term_ite(mathsatEnv, pBits);
  }

  private boolean isAtom(Long t) {
    return msat_term_is_atom(mathsatEnv, t);
  }

  private int getArity(Long pF) {
    return msat_term_arity(pF);
  }

  private BooleanFormula getArg(Long pF, int index) {
    assert getFormulaCreator().getBoolType().equals(getFormulaCreator().getFormulaType(pF));
    return getFormulaCreator().encapsulateBoolean(msat_term_get_arg(pF, index));
  }

  private List<BooleanFormula> getAllArgs(Long pF) {
    int arity = getArity(pF);
    List<BooleanFormula> args = new ArrayList<>(arity);
    for (int i = 0; i < arity; i++) {
      args.add(getArg(pF, i));
    }
    return args;
  }

  @Override
  protected <R> R visit(BooleanFormulaVisitor<R> pVisitor, Long f) {
    if (isTrue(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitTrue();
    }

    if (isFalse(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitFalse();
    }

    if (isNot(f)) {
      assert getArity(f) == 1;
      return pVisitor.visitNot(getArg(f, 0));
    }

    if (isAnd(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitTrue();
      } else if (getArity(f) == 1) {
        return visit(pVisitor, getArg(f, 0));
      }
      return pVisitor.visitAnd(getAllArgs(f));
    }

    if (isOr(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitFalse();
      } else if (getArity(f) == 1) {
        return pVisitor.visit(getArg(f, 0));
      }
      return pVisitor.visitOr(getAllArgs(f));
    }

    if (isEquivalence(f)) {
      assert getArity(f) == 2;
      return pVisitor.visitEquivalence(getArg(f, 0), getArg(f, 1));
    }

    if (isIfThenElse(f)) {
      assert getArity(f) == 3;
      return pVisitor.visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));
    }

    if (isAtom(f)) {
      return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));
    }

    throw new UnsupportedOperationException("Unknown or unsupported boolean operator " + f);
  }
}
