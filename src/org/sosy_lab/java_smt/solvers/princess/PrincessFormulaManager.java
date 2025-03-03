// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.IFormula;
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
        null,
        null,
        null);
    creator = pCreator;
  }

  BooleanFormula encapsulateBooleanFormula(IExpression t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public IExpression parseImpl(String pS) throws IllegalArgumentException {
    List<? extends IExpression> formulas = getEnvironment().parseStringToTerms(pS, creator);
    Preconditions.checkState(
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
