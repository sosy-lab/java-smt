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

import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;



/*
This is a wrapper class to use the different classes of dReal to create Formulas. In dReal we
have Variables, Expression and Formulas. To create a Formula, Variables and Expressions are
needed. Because in FormulaCreator there is only one excepted type, this wrapper class is needed,
so that all three types are available.  
 */
public class DRealTerm<Term> {

  // This is the term, so a Variable, an Expression or a Formula.
  private final Term term;
  // Here the declarationKind is stored, (3 * x) the kind is multiplication.

  // Type of the Variable, Expression or Formula
  private final Variable.Type type;

  public DRealTerm(Term pTerm, Variable.Type pType) {
    this.term = pTerm;
    this.type = pType;
  }

  public boolean isVar() {
    return term instanceof Variable;
  }

  public boolean isExp() {
    return term instanceof Expression;
  }

  public boolean isFormula() {
    return term instanceof Formula;
  }

  public Variable getVariable() {
    if (isVar()) {
      return (Variable) term;
    } else {
      throw new IllegalArgumentException("Not a Variable.");
    }
  }

  public Expression getExpression() {
    if (isExp()) {
      return (Expression) term;
    } else {
      throw new IllegalArgumentException("Not an Expression.");
    }
  }

  public Formula getFormula() {
    if (isFormula()) {
      return (Formula) term;
    } else {
      throw new IllegalArgumentException("Not a Formula.");
    }
  }

  public Variable.Type getType() {
    return type;
  }

  public ExpressionKind getExpressionKind() {
    if (isExp()) {
      Expression exp = (Expression) term;
      return exp.get_kind();
    } else {
      throw new IllegalArgumentException("Not an Expression.");
    }
  }

  public FormulaKind getFormulaKind() {
    if (isFormula()) {
      Formula formula = (Formula) term;
      return formula.get_kind();
    } else {
      throw new IllegalArgumentException("Not a Formula.");
    }
  }

  public String to_string() {
    if (isVar()) {
      Variable var = (Variable) term;
      return var.to_string();
    } else if (isExp()) {
      Expression exp = (Expression) term;
      return exp.to_string();
    } else {
      Formula formula = (Formula) term;
      return formula.to_string();
    }
  }


}
