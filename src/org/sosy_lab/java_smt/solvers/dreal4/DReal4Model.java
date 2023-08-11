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

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionDoubleMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionExpressionMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.VariableSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;


public class DReal4Model extends AbstractModel<DRealTerm<?>, Variable.Type, Context> {

  private final Box model;
  private final DReal4FormulaCreator formulaCreator;

  @SuppressWarnings("unused")
  private final DReal4TheoremProver prover;
  private final ImmutableList<DRealTerm<?>> assertedFormulas;

  DReal4Model(DReal4TheoremProver prover, DReal4FormulaCreator pCreator, Box model,
              Collection<DRealTerm<?>> pAssertedFormulas) {
    super(prover, pCreator);
    // create a copy of the model, because the model changes, if the context is used somewhere
    // else, the values we get out of it might change
    this.model = new Box(model);
    this.prover = prover;
    this.formulaCreator = pCreator;
    this.assertedFormulas = ImmutableList.copyOf(pAssertedFormulas);
  }

  @Override
  protected @Nullable DRealTerm<?> evalImpl(DRealTerm<?> formula) {
    // this will return a constant for the result of the variable
    if (formula.isVar()) {
      Variable variable = formula.getVariable();
      // if we find a variable that is not in the model, abort
      if (!model.has_variable(variable)) {
        return null;
      }
      Double res = extractResultsVariable(variable);
      if (res.isNaN()) {
        // When is result "EMPTY"?
        return null;
      } else {
        if (variable.get_type() == Variable.Type.BOOLEAN) {
          if (res > 0) {
            return new DRealTerm<>(Formula.True(), formula.getType());
          } else {
            return new DRealTerm<>(Formula.False(), formula.getType());
          }
        } else {
          return new DRealTerm<>(new Expression(res), formula.getType());
        }
      }
    } else if (formula.isExp()) {
      // this will return the constant of the Expression -> if expression is (x + 1) and x
      // evaluates to 5, it will return 6 and not (5+1)
      Expression exp = formula.getExpression();
      // if expression is already a constant, just return it
      if (exp.get_kind() == ExpressionKind.Constant) {
        return new DRealTerm<>(exp, formula.getType());
      } else if (exp.get_kind() == ExpressionKind.Var) {
        // we only get one variable back
        Variable var = dreal.get_variable(exp);
        return new DRealTerm<>(evalImpl(new DRealTerm<>(var, var.get_type())), var.get_type());
      } else {
        VariableSet expSet = exp.getVariables();
        for (Variable var : expSet) {
          // if we find a variable that is not in the model, abort
          if (!model.has_variable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          // TODO: can expression have a variable of boolean type?
          Preconditions.checkState(formula.getType() != Variable.Type.BOOLEAN);
          exp = substituteExpWithResult(exp, var, res);
          if (exp == null) {
            return null;
          }
        }
        return new DRealTerm<>(exp, formula.getType());
      }
    } else {
      // this will always return a True formula
      Formula f = formula.getFormula();
      // if formula is already true or false, just return the formula
      if (f.get_kind() == FormulaKind.True || f.get_kind() == FormulaKind.False) {
        return new DRealTerm<>(f, formula.getType());
      } else if (f.get_kind() == FormulaKind.Var) {
        // we only get one Variable back
        Variable var = dreal.get_variable(f);
        return new DRealTerm<>(evalImpl(new DRealTerm<>(var, var.get_type())), var.get_type());
        // we can only get quantified Variables if the Formula is a forall formula. So if we have
        // a Formula like (x == 10 and forall{y}.y == y } evalImpl does not work
      } else if (f.get_kind() == FormulaKind.Forall) {
        VariableSet quantifiedVars = f.getQuantifiedVariables();
        for (Variable var : quantifiedVars) {
          // if we find a variable that is not in the model, abort
          if (!model.has_variable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          f = substituteFormulaWithResult(f, var, res);
          if (f == null) {
            return null;
          }
        }
        return new DRealTerm<>(f, formula.getType());
      } else {
        VariableSet freeVars = f.getFreeVariables();
        for (Variable var : freeVars) {
          // if we find a variable that is not in the model, abort
          if (!model.has_variable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          f = substituteFormulaWithResult(f, var, res);
          if (f == null) {
            return null;
          }
        }
        return new DRealTerm<>(f, formula.getType());
      }
    }
  }

  private Expression substituteExpWithResult(Expression exp, Variable var, Double res) {
    if (res.isNaN()) {
      // When is result "EMPTY"?
      return null;
    } else {
      exp =  exp.Substitute(var, new Expression(res));
      return exp;
    }
  }

  private Formula substituteFormulaWithResult(Formula f, Variable var, Double res) {
    if (res.isNaN()) {
      // When is result "EMPTY"?
      return null;
    } else {
      if (var.get_type() == Variable.Type.BOOLEAN) {
        if (res > 0) {
          f = f.Substitute(var, Formula.True());
        } else {
          f = f.Substitute(var, Formula.False());
        }
      } else {
        f = f.Substitute(var, new Expression(res));
      }
      return f;
    }
  }

  /**
   * This function extracts the results of a formula. The function takes the variable and calls
   * getResult to get the value associated with the variable from the box.
   * @param var Variable to get the result from
   * @return Double as result
   */
  private Double extractResultsVariable(Variable var) {
    return parseResult(dreal.getResult(model, var));
  }

  private Double parseResult(String string) {
    if (string.equals("EMPTY")) {
      return Double.NaN;
    } else if (string.equals("ENTIRE")) {
      // probably unnecassary, and what should I return?
      return Double.valueOf(1);
    } else {
      String[] numbers = string.split(",", -1);
      return Double.valueOf(numbers[0] + "." + numbers[1]);

    }
  }

  // x + 2 = 10 dann ist KeyFormula = x und ValueFormel = 8 (beides Formulas). Die
  // BooleanFormula die gesamte Formel und value = 8 als JavaInterpretation
  // Brauche alle asserted formulas,
  @Override
  public ImmutableList<ValueAssignment> asList() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (DRealTerm<?> term : assertedFormulas) {
      recursiveAssignmentFinder(builder, term);
    }
    return builder.build().asList();
  }

  private void recursiveAssignmentFinder(ImmutableSet.Builder<ValueAssignment> builder,
                                         DRealTerm<?> term) {
    if (term.isVar()) {
      builder.add(getAssignment(term));
    } else if (term.isExp()) {
      ExpressionKind expKind = term.getExpressionKind();
      if (expKind == ExpressionKind.Constant) {
        return;
      } else if (expKind == ExpressionKind.Var) {
        Variable var = dreal.get_variable(term.getExpression());
        builder.add(getAssignment(new DRealTerm<>(var, var.get_type())));
      } else if (expKind == ExpressionKind.Pow) {
        Expression lhs = dreal.get_first_argument(term.getExpression());
        recursiveAssignmentFinder(builder,
            new DRealTerm<>(lhs, term.getType()));
      } else if (expKind == ExpressionKind.Div) {
        Expression firstArg = dreal.get_first_argument(term.getExpression());
        Expression secondArg = dreal.get_second_argument(term.getExpression());
        recursiveAssignmentFinder(builder, new DRealTerm<>(firstArg, term.getType()));
        recursiveAssignmentFinder(builder, new DRealTerm<>(secondArg, term.getType()));
      } else if (expKind == ExpressionKind.IfThenElse) {
        Formula cond = dreal.get_conditional_formula(term.getExpression());
        Expression expThen = dreal.get_then_expression(term.getExpression());
        Expression expElse = dreal.get_else_expression(term.getExpression());
        recursiveAssignmentFinder(builder, new DRealTerm<>(cond, term.getType()));
        recursiveAssignmentFinder(builder, new DRealTerm<>(expThen, term.getType()));
        recursiveAssignmentFinder(builder, new DRealTerm<>(expElse, term.getType()));
      } else if (expKind == ExpressionKind.Add) {
        // We have map of Expression and Double. Expression is the variable and Double the
        // constant of the addition. (2*x + 3*y) We can ignore the double value and only
        // recursively call the assignment finder. If we have constant in addition, we ignore the
        // constant as well (not a call to get the constant, get_constant_in_addition(Expression
        // exp))
        ExpressionDoubleMap map = dreal.get_expr_to_coeff_map_in_addition(term.getExpression());
        for (Map.Entry<Expression, Double> entry : map.entrySet()) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(entry.getKey(), term.getType()));
        }
      } else if (expKind == ExpressionKind.Mul) {
        // We get a map of Expression and Expression with the second Expression being the
        // exponent of the Variable. The exponent is ignored. The constant is ignored, no call
        // get_constant_in_multiplication
        ExpressionExpressionMap map =
            dreal.get_base_to_exponent_map_in_multiplication(term.getExpression());
        for (Map.Entry<Expression, Expression> entry : map.entrySet()) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(entry.getKey(), term.getType()));
        }
      } else if (expKind == ExpressionKind.UninterpretedFunction) {
        throw new UnsupportedOperationException("Not implemented yet");
      } else {
        throw new IllegalArgumentException("Failure visiting the Term " + term.to_string() + " .");
      }
    } else {
      FormulaKind fKind = term.getFormulaKind();
      if (fKind == FormulaKind.Var) {
        Variable var = dreal.get_variable(term.getFormula());
        builder.add(getAssignment(new DRealTerm<>(var, var.get_type())));
      } else if (fKind == FormulaKind.True || fKind == FormulaKind.False) {
        return;
      } else if (fKind == FormulaKind.Not) {
        Formula fNot = dreal.get_operand(term.getFormula());
        recursiveAssignmentFinder(builder, new DRealTerm<>(fNot, term.getType()));
      } else if (fKind == FormulaKind.Eq
          || fKind == FormulaKind.Gt
          || fKind == FormulaKind.Geq
          || fKind == FormulaKind.Lt
          || fKind == FormulaKind.Leq
          || fKind == FormulaKind.Neq) {
        Expression leftChild = dreal.get_lhs_expression(term.getFormula());
        Expression rightChild = dreal.get_rhs_expression(term.getFormula());
        Variable.Type type;
        type = DReal4FormulaCreator.getTypeForExpressions(leftChild);
        // if type is null, we did not find a variable in left child, we can ignore the formula,
        // else both child could have variable
        if (type == null) {
          type = DReal4FormulaCreator.getTypeForExpressions(rightChild);
          recursiveAssignmentFinder(builder, new DRealTerm<>(rightChild, type));
        } else {
          recursiveAssignmentFinder(builder, new DRealTerm<>(leftChild, type));
          recursiveAssignmentFinder(builder, new DRealTerm<>(rightChild, type));
        }
      } else if (fKind == FormulaKind.And || fKind == FormulaKind.Or) {
        FormulaSet fSet = dreal.get_operands(term.getFormula());
        for (Formula f : fSet) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(f, term.getType()));
        }
      } else {
        //We only go through the bound variables, because we have a quantified formula
        VariableSet varSet = term.getFormula().getQuantifiedVariables();
        for (Variable var : varSet) {
          builder.add(getAssignment(new DRealTerm<>(var, var.get_type())));
        }
      }

    }
  }

  private ValueAssignment getAssignment(DRealTerm<?> term) {
    // valueTerm should be a variable
    Preconditions.checkState(term.isVar());
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    // valueTerm can be Formula or Expression
    DRealTerm<?> valueTerm = evalImpl(term);
    org.sosy_lab.java_smt.api.Formula keyFormula = formulaCreator.encapsulateWithTypeOf(term);
    org.sosy_lab.java_smt.api.Formula valueFormula =
        formulaCreator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation;
    if (valueTerm.isExp()) {
      equation =
          creator.encapsulateBoolean(new DRealTerm<>(
              new Formula(dreal.Equal(new Expression(term.getVariable()),
                  valueTerm.getExpression())), Variable.Type.BOOLEAN));
    } else if (valueTerm.isFormula()) {
      equation =
          creator.encapsulateBoolean(new DRealTerm<>(
              new Formula(dreal.Equal(term.getVariable(),
                  valueTerm.getFormula())), Variable.Type.BOOLEAN));
    } else {
      throw new UnsupportedOperationException("Trying to get an Assignment from an Expression " + term.to_string() + " .");
    }
    Object value = formulaCreator.convertValue(valueTerm);
    return new ValueAssignment(keyFormula, valueFormula, equation, term.getVariable().get_name(),
        value, argumentInterpretationBuilder.build());
  }

}