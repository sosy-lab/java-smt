// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class CVC4RationalFormulaManager
    extends CVC4NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  CVC4RationalFormulaManager(
      CVC4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Type getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Expr makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Expr makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  @Override
  public Expr divide(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.DIVISION, pParam1, pParam2);
  }

  @Override
  protected Expr floor(Expr pNumber) {
    return exprManager.mkExpr(Kind.TO_INTEGER, pNumber);
  }
}
