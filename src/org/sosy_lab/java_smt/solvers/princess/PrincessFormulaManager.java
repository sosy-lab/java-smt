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
import ap.parser.IEquation;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.Rewriter;
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
  protected IExpression equalImpl(IExpression pArg1, IExpression pArg2) {
    if (pArg1 instanceof IFormula) {
      return new IBinFormula(IBinJunctor.Eqv(), (IFormula) pArg1, (IFormula) pArg2);
    } else if (pArg2 instanceof IIntLit && ((IIntLit) pArg2).value().isZero()) {
      return IExpression.eqZero((ITerm) pArg1);
    } else {
      return ((ITerm) pArg1).$eq$eq$eq((ITerm) pArg2);
    }
  }

  @Override
  public IExpression parseImpl(String pS) throws IllegalArgumentException {
    List<? extends IExpression> formulas = getEnvironment().parseStringToTerms(pS, creator);
    Preconditions.checkArgument(
        formulas.size() == 1,
        "parsing expects exactly one asserted term, but got %s terms",
        formulas.size());
    // Rewrite (= term 0) to (=0 term)
    return Rewriter.rewrite(
        formulas.get(0),
        term -> {
          if (term instanceof IEquation) {
            var equation = (IEquation) term;
            if (equation.right() instanceof IIntLit
                && ((IIntLit) equation.right()).value().isZero()) {
              return IExpression.eqZero(equation.left());
            }
          }
          return term;
        });
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
