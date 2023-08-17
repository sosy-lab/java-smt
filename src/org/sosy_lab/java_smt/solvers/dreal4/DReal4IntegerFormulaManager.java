// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public class DReal4IntegerFormulaManager
    extends DReal4NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  DReal4IntegerFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Variable.Type getNumeralType() {
    return getFormulaCreator().getIntegerType();
  }

  // Division with Integer can be a problem. See Issue 304
  // (https://github.com/dreal/dreal4/issues/304).
  // With two Constant being divided it is manually rounded off, but if we have a division with a
  // variable,
  // it is not real integer division. Therefore it could result in wrong results. Use with caution.
  @Override
  public DRealTerm<Expression, ExpressionKind> divide(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      if (pParam1.getExpressionKind() == ExpressionKind.Constant
          && pParam2.getExpressionKind() == ExpressionKind.Constant) {
        if (Double.parseDouble(pParam2.toString()) == 0.0) {
          throw new IllegalArgumentException("dReal does not support division by zero.");
        }
        double dParam1 = Double.parseDouble(pParam1.getExpression().to_string());
        double dParam2 = Double.parseDouble(pParam2.getExpression().to_string());
        int res = (int) (dParam1 / dParam2);
        return new DRealTerm<>(new Expression(res), Variable.Type.INTEGER, ExpressionKind.Constant);
      }
      return new DRealTerm<>(
          dreal.Divide(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Div);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      if (pParam2.getExpressionKind() == ExpressionKind.Constant) {
        if (Double.parseDouble(pParam2.toString()) == 0.0) {
          throw new IllegalArgumentException("dReal does not support division by zero.");
        }
      }
      return new DRealTerm<>(
          dreal.Divide(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Div);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Divide(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Div);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Divide(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Div);
    } else {
      throw new UnsupportedOperationException("dReal does not support divide with Formulas.");
    }
  }

  // Use with caution, because of integer division. Integer division is not real integer division,
  // therefore the results could be incorrect
  @Override
  protected DRealTerm<?, ?> modularCongruence(
      DRealTerm<?, ?> pNumber1, DRealTerm<?, ?> pNumber2, BigInteger pModulo) {
    return modularCongruence0(pNumber1, pNumber2, pModulo.toString());
  }

  @Override
  protected DRealTerm<?, ?> modularCongruence(
      DRealTerm<?, ?> pNumber1, DRealTerm<?, ?> pNumber2, long pModulo) {
    return modularCongruence0(pNumber1, pNumber2, Long.toString(pModulo));
  }

  protected DRealTerm<?, ?> modularCongruence0(
      DRealTerm<?, ?> pNumber1, DRealTerm<?, ?> pNumber2, String pModulo) {
    // ((_ divisible n) x) <==> (= x (* n (div x n)))
    DRealTerm<Expression, ExpressionKind> mod = makeNumberImpl(pModulo);
    DRealTerm<Expression, ExpressionKind> sub = subtract(pNumber1, pNumber2);
    DRealTerm<Expression, ExpressionKind> div = divide(sub, mod);
    DRealTerm<Expression, ExpressionKind> mul = multiply(mod, div);
    return equal(sub, mul);
  }
}
