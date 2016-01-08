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
package org.sosy_lab.solver.princess;

import static com.google.common.collect.Iterables.getOnlyElement;

import ap.parser.BooleanCompactifier;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.PartialEvaluator;

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;


final class PrincessFormulaManager
    extends AbstractFormulaManager<IExpression, TermType, PrincessEnvironment> {

  @SuppressWarnings("checkstyle:parameternumber")
  PrincessFormulaManager(
      PrincessFormulaCreator pCreator,
      PrincessUnsafeFormulaManager pUnsafeManager,
      PrincessFunctionFormulaManager pFunctionManager,
      PrincessBooleanFormulaManager pBooleanManager,
      PrincessIntegerFormulaManager pIntegerManager,
      PrincessArrayFormulaManager pArrayManager,
      PrincessQuantifiedFormulaManager pQuantifierManager) {
    super(
        pCreator,
        pUnsafeManager,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        null,
        null,
        null,
        pQuantifierManager,
        pArrayManager);
  }

  BooleanFormula encapsulateBooleanFormula(IExpression t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }


  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    return encapsulateBooleanFormula(getOnlyElement(getEnvironment().parseStringToTerms(pS)));
  }

  @Override
  public Appender dumpFormula(final IExpression formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return getEnvironment().dumpFormula((IFormula) formula);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> rFormulaVisitor, Formula f) {
    return getUnsafeFormulaManager().visit(rFormulaVisitor, f);
  }

  @Override
  protected IExpression simplify(IExpression f) {
    // TODO this method is not tested, check it!
    if (f instanceof IFormula) {
      f = BooleanCompactifier.apply((IFormula) f);
    }
    return PartialEvaluator.apply(f);
  }
}
