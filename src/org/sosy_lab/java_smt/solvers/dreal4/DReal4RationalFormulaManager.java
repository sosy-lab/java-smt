/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.dreal4;

import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public class DReal4RationalFormulaManager
    extends DReal4NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  DReal4RationalFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Variable.Type getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  public DRealTerm<Expression, ExpressionKind> divide(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      if (pParam1.getExpressionKind() == ExpressionKind.Constant
          && pParam2.getExpressionKind() == ExpressionKind.Constant) {
        if (Double.parseDouble(pParam2.to_string()) == 0.0) {
          throw new IllegalArgumentException("dReal does not support division by zero.");
        }
        return new DRealTerm<>(
            dreal.Divide(pParam1.getExpression(), pParam2.getExpression()),
            pParam1.getType(),
            ExpressionKind.Div);
      }
      return new DRealTerm<>(
          dreal.Divide(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Div);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      if (pParam2.getExpressionKind() == ExpressionKind.Constant) {
        if (Double.parseDouble(pParam2.to_string()) == 0.0) {
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

  // Also not possible to change the type of a variable, therefore not possible to hard code
  // (forall{x}. floor(x) <= x) would not be a tautology, because floor(x) would create a new
  // variable with integer type, but would not have a reference to x.
  @Override
  protected DRealTerm<?, ?> floor(DRealTerm<?, ?> number) {
    throw new UnsupportedOperationException("dReal does not support floor.");
  }
}
