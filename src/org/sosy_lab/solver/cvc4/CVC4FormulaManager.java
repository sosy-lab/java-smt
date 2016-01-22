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
package org.sosy_lab.solver.cvc4;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.List;
import java.util.Map;

class CVC4FormulaManager extends AbstractFormulaManager<Expr, Type, CVC4Environment> {

  CVC4FormulaManager(
      FormulaCreator<Expr, Type, CVC4Environment> pFormulaCreator,
      CVC4FunctionFormulaManager pFfmgr,
      CVC4BooleanFormulaManager pBfmgr,
      CVC4IntegerFormulaManager pIfmgr) {
    super(pFormulaCreator, pFfmgr, pBfmgr, pIfmgr, null, null, null, null, null);
  }

  static Expr getCVC4Expr(Formula pT) {
    if (pT instanceof CVC4Formula) {
      return ((CVC4Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  BooleanFormula encapsulateBooleanFormula(Expr t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Appender dumpFormula(Expr pT) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected List<? extends Expr> splitNumeralEqualityIfPossible(Expr pF) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  public Formula substitute(Formula pF, Map<Formula, Formula> pFromToMapping) {
    return substituteUsingMap(pF, pFromToMapping);
  }
}
