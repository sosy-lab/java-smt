// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

/*
This is a wrapper class to use the different classes of dReal to create Formulas. In dReal we
have Variables, Expression and Formulas. To create a Formula, Variables and Expressions are
needed. Because in FormulaCreator there is only one excepted type, this wrapper class is needed,
so that all three types are available.
 */
public class DRealTerm<Term, Declaration> {

  // This is the term, so a Variable, an Expression or a Formula.
  private final Term term;
  // Type of the Variable, Expression or Formula
  private final Variable.Type type;
  // Here the declarationKind is stored, (3 * x) the kind is multiplication. Is only needed for
  // visitor
  private final Declaration declaration;

  public DRealTerm(Term pTerm, Variable.Type pType, Declaration pDeclaration) {
    this.term = pTerm;
    this.type = pType;
    this.declaration = pDeclaration;
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

  public Declaration getDeclaration() {
    return declaration;
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

  @Override
  public String toString() {
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

  @Override
  public final int hashCode() {
    if (isExp()) {
      return (int) getExpression().get_hash();
    } else if (isFormula()) {
      return (int) getFormula().get_hash();
    } else {
      return (int) getVariable().get_hash();
    }
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof DReal4Formula)) {
      return false;
    }
    // equal_to only checks for the same structure
    DRealTerm<?, ?> oTerm = ((DReal4Formula) o).getTerm();
    if (isVar()) {
      if (oTerm.isVar()) {
        return getVariable().equal_to(oTerm.getVariable());
      } else if (oTerm.isExp()) {
        if (oTerm.getExpressionKind() == ExpressionKind.Var) {
          return getVariable().equal_to(dreal.get_variable(oTerm.getExpression()));
        }
      } else {
        if (oTerm.getFormulaKind() == FormulaKind.Var) {
          return getVariable().equal_to(dreal.get_variable(oTerm.getFormula()));
        }
      }
    } else if (isExp()) {
      if (getExpressionKind() == ExpressionKind.Var) {
        if (oTerm.isVar()) {
          return oTerm.getVariable().equal_to(dreal.get_variable(getExpression()));
        } else if (oTerm.isExp()) {
          return getExpression().EqualTo(oTerm.getExpression());
        } else {
          if (oTerm.getFormulaKind() == FormulaKind.Var) {
            return dreal
                .get_variable(getExpression())
                .equal_to(dreal.get_variable(oTerm.getFormula()));
          }
        }
      } else {
        if (oTerm.isExp()) {
          return getExpression().EqualTo(oTerm.getExpression());
        }
      }
    } else {
      if (getFormulaKind() == FormulaKind.Var) {
        if (oTerm.isVar()) {
          return oTerm.getVariable().equal_to(dreal.get_variable(getFormula()));
        } else if (oTerm.isExp()) {
          if (oTerm.getExpressionKind() == ExpressionKind.Var) {
            return dreal
                .get_variable(getFormula())
                .equal_to(dreal.get_variable(oTerm.getExpression()));
          }
        } else {
          if (oTerm.getFormulaKind() == FormulaKind.Var) {
            return dreal
                .get_variable(getFormula())
                .equal_to(dreal.get_variable(oTerm.getFormula()));
          }
        }
      } else {
        if (oTerm.isFormula()) {
          return getFormula().EqualTo(oTerm.getFormula());
        }
      }
    }
    return false;
  }
}
