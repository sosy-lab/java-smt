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

import javax.annotation.Nullable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;

public class DRealTerm {

  @Nullable
  private Variable var;
  @Nullable
  private Expression exp;
  @Nullable
  private Formula formula;

  public DRealTerm(Variable pVar, Expression pExp, Formula pFormula) {
    this.var = pVar;
    this.exp = pExp;
    this.formula = pFormula;
  }

  public boolean isVar() {
    return var != null;
  }

  public boolean isExp() {
    return exp != null;
  }

  public boolean isFormula() {
    return formula != null;
  }

  public Variable getVariable() {
    return var;
  }

  public Expression getExpression() {
    return exp;
  }

  public Formula getFormula() {
    return formula;
  }

  public Type getVariableKind() {
    return var.get_type();
  }

  public ExpressionKind getExpressionKind() {
    return exp.get_kind();
  }

  public FormulaKind getFormulaKind() {
    return formula.get_kind();
  }
}
