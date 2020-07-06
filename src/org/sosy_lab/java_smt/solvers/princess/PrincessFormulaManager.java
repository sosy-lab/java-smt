// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.collect.Iterables.getOnlyElement;

import ap.parser.BooleanCompactifier;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.PartialEvaluator;
import ap.types.Sort;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class PrincessFormulaManager
    extends AbstractFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final PrincessFormulaCreator creator;

  @SuppressWarnings("checkstyle:parameternumber")
  PrincessFormulaManager(
      PrincessFormulaCreator pCreator,
      PrincessUFManager pFunctionManager,
      PrincessBooleanFormulaManager pBooleanManager,
      PrincessIntegerFormulaManager pIntegerManager,
      PrincessBitvectorFormulaManager pBitpreciseManager,
      PrincessArrayFormulaManager pArrayManager,
      PrincessQuantifiedFormulaManager pQuantifierManager) {
    super(
        pCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        null,
        pBitpreciseManager,
        null,
        pQuantifierManager,
        pArrayManager,
        null);
    creator = pCreator;
  }

  BooleanFormula encapsulateBooleanFormula(IExpression t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    return encapsulateBooleanFormula(
        getOnlyElement(getEnvironment().parseStringToTerms(pS, creator)));
  }

  @Override
  public Appender dumpFormula(final IExpression formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return getEnvironment().dumpFormula((IFormula) formula, creator);
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
