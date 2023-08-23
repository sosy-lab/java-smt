// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;

public class DReal4RationalFormulaManager
    extends DReal4NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  DReal4RationalFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Variable.Type.Kind getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  public DRealTerm<Expression, ExpressionKind.ExpressionType> divide(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      if (pParam1.getExpressionKind() == ExpressionKind.CONSTANT
          && pParam2.getExpressionKind() == ExpressionKind.CONSTANT) {
        Preconditions.checkArgument(
            Double.parseDouble(pParam2.toString()) != 0.0,
            "dReal does " + "not support " + "division by zero.");
        return new DRealTerm<>(
            Dreal.divide(pParam1.getExpression(), pParam2.getExpression()),
            pParam1.getType(),
            ExpressionKind.DIV);
      }
      return new DRealTerm<>(
          Dreal.divide(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.DIV);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      if (pParam2.getExpressionKind() == ExpressionKind.CONSTANT) {
        Preconditions.checkArgument(
            Double.parseDouble(pParam2.toString()) != 0.0,
            "dReal does " + "not support " + "division by zero.");
      }
      return new DRealTerm<>(
          Dreal.divide(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.DIV);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.divide(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.DIV);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.divide(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.DIV);
    } else {
      throw new UnsupportedOperationException("dReal does not support to divide with Formulas.");
    }
  }

  // Also not possible to change the type of a variable, therefore not possible to hard code
  // (forall{x}. floor(x) <= x) would not be a tautology, because floor(x) would create a new
  // variable with integer type, but would not have a reference to x.
  @Override
  protected DRealTerm<?, ?> floor(DRealTerm<?, ?> number) {
    throw new UnsupportedOperationException("dReal does not support floor.");
  }
}
