// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;

/*
This is a wrapper class to use the different classes of dReal to create Formulas. In dReal we
have Variables, Expression and Formulas. To create a Formula, Variables and Expressions are
needed. Because in FormulaCreator there is only one excepted type, this wrapper class is needed,
so that all three types are available.
 */
public class DRealTerm<T, D> {

  // This is the term, so a Variable, an Expression or a Formula.
  private final T term;
  // Type of the Variable, Expression or Formula
  private final Variable.Type.Kind type;
  // Here the declarationKind is stored, (3 * x) the kind is multiplication. Is only needed for
  // visitor
  private final D declaration;

  public DRealTerm(T pTerm, Variable.Type.Kind pType, D pDeclaration) {
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

  public Variable.Type.Kind getType() {
    return type;
  }

  public D getDeclaration() {
    return declaration;
  }

  public ExpressionKind.ExpressionType getExpressionKind() {
    if (isExp()) {
      Expression exp = (Expression) term;
      return exp.getKind();
    } else {
      throw new IllegalArgumentException("Not an Expression.");
    }
  }

  public FormulaKind.FormulaType getFormulaKind() {
    if (isFormula()) {
      Formula formula = (Formula) term;
      return formula.getKind();
    } else {
      throw new IllegalArgumentException("Not a Formula.");
    }
  }

  @Override
  public String toString() {
    if (isVar()) {
      Variable var = (Variable) term;
      return var.toString();
    } else if (isExp()) {
      Expression exp = (Expression) term;
      return exp.toString();
    } else {
      Formula formula = (Formula) term;
      return formula.toString();
    }
  }

  @Override
  public final int hashCode() {
    if (isExp()) {
      return (int) getExpression().getHash();
    } else if (isFormula()) {
      return (int) getFormula().getHash();
    } else {
      return (int) getVariable().getHash();
    }
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (o instanceof DRealTerm) {
      // equal_to only checks for the same structure
      DRealTerm<?, ?> oTerm = ((DRealTerm<?, ?>) o);
      if (isVar()) {
        if (oTerm.isVar()) {
          return getVariable().equalTo(oTerm.getVariable());
        } else if (oTerm.isExp()) {
          if (oTerm.getExpressionKind() == ExpressionKind.VAR) {
            return getVariable().equalTo(Dreal.getVariable(oTerm.getExpression()));
          }
        } else {
          if (oTerm.getFormulaKind() == FormulaKind.VAR) {
            return getVariable().equalTo(Dreal.getVariable(oTerm.getFormula()));
          }
        }
      } else if (isExp()) {
        if (getExpressionKind() == ExpressionKind.VAR) {
          if (oTerm.isVar()) {
            return oTerm.getVariable().equalTo(Dreal.getVariable(getExpression()));
          } else if (oTerm.isExp()) {
            return getExpression().equalTo(oTerm.getExpression());
          } else {
            if (oTerm.getFormulaKind() == FormulaKind.VAR) {
              return Dreal.getVariable(getExpression())
                  .equalTo(Dreal.getVariable(oTerm.getFormula()));
            }
          }
        } else {
          if (oTerm.isExp()) {
            return getExpression().equalTo(oTerm.getExpression());
          }
        }
      } else {
        if (getFormulaKind() == FormulaKind.VAR) {
          if (oTerm.isVar()) {
            return oTerm.getVariable().equalTo(Dreal.getVariable(getFormula()));
          } else if (oTerm.isExp()) {
            if (oTerm.getExpressionKind() == ExpressionKind.VAR) {
              return Dreal.getVariable(getFormula())
                  .equalTo(Dreal.getVariable(oTerm.getExpression()));
            }
          } else {
            if (oTerm.getFormulaKind() == FormulaKind.VAR) {
              return Dreal.getVariable(getFormula()).equalTo(Dreal.getVariable(oTerm.getFormula()));
            }
          }
        } else {
          if (oTerm.isFormula()) {
            return getFormula().equalTo(oTerm.getFormula());
          }
        }
      }
    } else {
      return false;
    }
    return false;
  }
}
