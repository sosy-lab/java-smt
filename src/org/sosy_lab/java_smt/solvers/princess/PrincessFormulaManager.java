// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;
import ap.types.Sort;
import com.google.common.base.Preconditions;
import java.io.IOException;
import java.util.List;
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
      PrincessRationalFormulaManager pRationalManager,
      PrincessBitvectorFormulaManager pBitpreciseManager,
      PrincessArrayFormulaManager pArrayManager,
      PrincessQuantifiedFormulaManager pQuantifierManager,
      PrincessStringFormulaManager pStringManager) {
    super(
        pCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        null,
        pQuantifierManager,
        pArrayManager,
        null,
        pStringManager,
        null);
    creator = pCreator;
  }

  BooleanFormula encapsulateBooleanFormula(IExpression t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  protected IExpression equalImpl(IExpression pArg1, IExpression pArgs2) {
    if (pArg1 instanceof IFormula) {
      return new IBinFormula(IBinJunctor.Eqv(), (IFormula) pArg1, (IFormula) pArgs2);
    } else {
      FormulaType<?> type1 = getFormulaCreator().getFormulaType(pArg1);
      FormulaType<?> type2 = getFormulaCreator().getFormulaType(pArgs2);
      if (type1.equals(type2)) { // identical types
        return ((ITerm) pArg1).$eq$eq$eq((ITerm) pArgs2);
      } else if (type1.isNumeralType() && type2.isNumeralType()) {
        // different types, but both are numerals, so we can compare them as rationals
        return ((PrincessRationalFormulaManager) getRationalFormulaManager()).equal(pArg1, pArgs2);
      } else {
        throw new IllegalArgumentException(
            String.format("Cannot compare formulas of different types: %s and %s", type1, type2));
      }
    }
  }

  @Override
  public IExpression parseImpl(String pS) throws IllegalArgumentException {
    List<? extends IExpression> formulas = getEnvironment().parseStringToTerms(pS, creator);
    Preconditions.checkArgument(
        formulas.size() == 1,
        "parsing expects exactly one asserted term, but got %s terms",
        formulas.size());
    return formulas.get(0);
  }

  @Override
  public String dumpFormulaImpl(final IExpression formula) throws IOException {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return getEnvironment().dumpFormula((IFormula) formula, creator);
  }

  @Override
  protected IExpression simplify(IExpression f) {
    return getEnvironment().simplify(f);
  }
}
