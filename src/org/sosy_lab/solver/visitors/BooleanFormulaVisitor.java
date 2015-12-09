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
package org.sosy_lab.solver.visitors;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.UnsafeFormulaManager;


public abstract class BooleanFormulaVisitor<R> {

  private final FormulaManager fmgr;
  private final BooleanFormulaManager bfmgr;
  private final UnsafeFormulaManager unsafe;

  protected BooleanFormulaVisitor(FormulaManager pFmgr) {
    fmgr = pFmgr;
    bfmgr = fmgr.getBooleanFormulaManager();
    unsafe = fmgr.getUnsafeFormulaManager();
  }

  public final R visit(BooleanFormula f) {
    if (bfmgr.isTrue(f)) {
      assert unsafe.getArity(f) == 0;
      return visitTrue();
    }

    if (bfmgr.isFalse(f)) {
      assert unsafe.getArity(f) == 0;
      return visitFalse();
    }

    if (unsafe.isAtom(f)) {
      return visitAtom(f);
    }

    if (bfmgr.isNot(f)) {
      assert unsafe.getArity(f) == 1;
      return visitNot(getArg(f, 0));
    }

    if (bfmgr.isAnd(f)) {
      if (unsafe.getArity(f) == 0) {
        return visitTrue();
      } else if (unsafe.getArity(f) == 1) {
        return visit(getArg(f, 0));
      }
      return visitAnd(getAllArgs(f));
    }

    if (bfmgr.isOr(f)) {
      if (unsafe.getArity(f) == 0) {
        return visitFalse();
      } else if (unsafe.getArity(f) == 1) {
        return visit(getArg(f, 0));
      }
      return visitOr(getAllArgs(f));
    }

    if (bfmgr.isEquivalence(f)) {
      assert unsafe.getArity(f) == 2;
      return visitEquivalence(getArg(f, 0), getArg(f, 1));
    }

    if (bfmgr.isImplication(f)) {
      assert unsafe.getArity(f) == 2;
      return visitImplication(getArg(f, 0), getArg(f, 1));
    }

    if (bfmgr.isIfThenElse(f)) {
      assert unsafe.getArity(f) == 3;
      return visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));
    }

    throw new UnsupportedOperationException("Unknown boolean operator " + f);
  }

  private BooleanFormula getArg(BooleanFormula pF, int i) {
    Formula arg = unsafe.getArg(pF, i);
    assert fmgr.getFormulaType(arg).isBooleanType();
    return (BooleanFormula)arg;
  }

  private BooleanFormula[] getAllArgs(BooleanFormula pF) {
    int arity = unsafe.getArity(pF);
    BooleanFormula[] args = new BooleanFormula[arity];
    for (int i = 0; i < arity; i++) {
      args[i] = getArg(pF, i);
    }
    return args;
  }

  protected abstract R visitTrue();
  protected abstract R visitFalse();
  protected abstract R visitAtom(BooleanFormula atom);
  protected abstract R visitNot(BooleanFormula operand);
  protected abstract R visitAnd(BooleanFormula... operands);
  protected abstract R visitOr(BooleanFormula... operand);
  protected abstract R visitEquivalence(BooleanFormula operand1, BooleanFormula operand2);
  protected abstract R visitImplication(BooleanFormula operand1, BooleanFormula operand2);
  protected abstract R visitIfThenElse(BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula);
}