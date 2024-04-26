// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionDoubleMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionExpressionMap;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.VariableSet;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;

public class DReal4Model extends AbstractModel<DRealTerm<?, ?>, Variable.Type.Kind, Config> {

  private final Box model;
  private final DReal4FormulaCreator formulaCreator;

  @SuppressWarnings("unused")
  private final DReal4TheoremProver prover;

  private final ImmutableList<DRealTerm<?, ?>> assertedFormulas;

  DReal4Model(
      DReal4TheoremProver prover,
      DReal4FormulaCreator pCreator,
      Box model,
      Collection<DRealTerm<?, ?>> pAssertedFormulas) {
    super(prover, pCreator);
    // create a copy of the model, because the model changes, if the context is used somewhere
    // else, the values we get out of it might change
    this.model = new Box(model);
    this.prover = prover;
    this.formulaCreator = pCreator;
    this.assertedFormulas = ImmutableList.copyOf(pAssertedFormulas);
  }

  @Override
  protected @Nullable DRealTerm<?, ?> evalImpl(DRealTerm<?, ?> formula) {
    // this will return a constant for the result of the variable
    if (formula.isVar()) {
      Variable variable = formula.getVariable();
      // if we find a variable that is not in the model, abort
      if (!model.hasVariable(variable)) {
        return null;
      }
      Double res = extractResultsVariable(variable);
      if (res.isNaN()) {
        // Result was "EMPTY"
        return null;
      } else {
        if (variable.getType() == Variable.Type.BOOLEAN) {
          if (res > 0) {
            return new DRealTerm<>(Formula.formulaTrue(), formula.getType(), FormulaKind.TRUE);
          } else {
            return new DRealTerm<>(Formula.formulaFalse(), formula.getType(), FormulaKind.TRUE);
          }
        } else {
          return new DRealTerm<>(new Expression(res), formula.getType(), ExpressionKind.CONSTANT);
        }
      }
    } else if (formula.isExp()) {
      // this will return the constant of the Expression -> if expression is (x + 1) and x
      // evaluates to 5, it will return 6 and not (5+1), because of rewrites in dReal
      Expression exp = formula.getExpression();
      // if expression is already a constant, just return it
      if (exp.getKind() == ExpressionKind.CONSTANT) {
        return new DRealTerm<>(exp, formula.getType(), ExpressionKind.CONSTANT);
      } else if (exp.getKind() == ExpressionKind.VAR) {
        // we only get one variable back
        Variable var = Dreal.getVariable(exp);
        return evalImpl(new DRealTerm<>(var, var.getType(), var.getType()));
      } else {
        Variables variables = exp.expressionGetVariables();
        DReal4FormulaCreator myCreator = (DReal4FormulaCreator) creator;
        for (Variable var : myCreator.toSet(variables)) {
          // if we find a variable that is not in the model, abort
          if (!model.hasVariable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          // expression can not have variable of boolean type
          Preconditions.checkState(formula.getType() != Variable.Type.BOOLEAN);
          exp = substituteExpWithResult(exp, var, res);
          if (exp == null) {
            return null;
          }
        }
        return new DRealTerm<>(exp, formula.getType(), exp.getKind());
      }
    } else {
      // this will always return a True formula, because of rewrites in dReal
      Formula f = formula.getFormula();
      if (f.getKind() == FormulaKind.TRUE || f.getKind() == FormulaKind.FALSE) {
        return new DRealTerm<>(f, formula.getType(), f.getKind());
      } else if (f.getKind() == FormulaKind.VAR) {
        // we only get one Variable back
        Variable var = Dreal.getVariable(f);
        return evalImpl(new DRealTerm<>(var, var.getType(), var.getType()));
        // we can only get quantified Variables if the Formula is a forall formula. So if we have
        // a Formula like (x == 10 and forall{y}.y == y } evalImpl does not work
      } else if (f.getKind() == FormulaKind.FORALL) {
        VariableSet quantifiedVars = f.getQuantifiedVariables();
        for (Variable var : quantifiedVars) {
          // if we find a variable that is not in the model, abort
          if (!model.hasVariable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          f = substituteFormulaWithResult(f, var, res);
          if (f == null) {
            return null;
          }
        }
        return new DRealTerm<>(f, formula.getType(), f.getKind());
      } else {
        VariableSet freeVars = f.getFreeVariables();
        for (Variable var : freeVars) {
          // if we find a variable that is not in the model, abort
          if (!model.hasVariable(var)) {
            return null;
          }
          Double res = extractResultsVariable(var);
          f = substituteFormulaWithResult(f, var, res);
          if (f == null) {
            return null;
          }
        }
        return new DRealTerm<>(f, formula.getType(), f.getKind());
      }
    }
  }

  private Expression substituteExpWithResult(Expression exp, Variable var, Double res) {
    if (res.isNaN()) {
      // result was "EMPTY"
      return null;
    } else {
      exp = exp.substitute(var, new Expression(res));
      return exp;
    }
  }

  private Formula substituteFormulaWithResult(Formula f, Variable var, Double res) {
    if (res.isNaN()) {
      // result was "EMTPY"
      return null;
    } else {
      if (var.getType() == Variable.Type.BOOLEAN) {
        if (res > 0) {
          f = f.substitute(var, Formula.formulaTrue());
        } else {
          f = f.substitute(var, Formula.formulaFalse());
        }
      } else {
        f = f.substitute(var, new Expression(res));
      }
      return f;
    }
  }

  /**
   * This function extracts the results of a formula. The function takes the variable and calls
   * getResult to get the value associated with the variable from the box.
   *
   * @param var Variable to get the result from
   * @return Double as result
   */
  private Double extractResultsVariable(Variable var) {
    return parseResult(Dreal.getResult(model, var));
  }

  private Double parseResult(String string) {
    if (string.equals("EMPTY")) {
      return Double.NaN;
    } else if (string.equals("ENTIRE")) {
      return Double.valueOf(1);
    } else {
      String[] numbers = string.split(",", -1);
      return Double.valueOf(numbers[0] + "." + numbers[1]);
    }
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (DRealTerm<?, ?> term : assertedFormulas) {
      recursiveAssignmentFinder(builder, term);
    }
    return builder.build().asList();
  }

  private void recursiveAssignmentFinder(
      ImmutableSet.Builder<ValueAssignment> builder, DRealTerm<?, ?> term) {
    if (term.isVar()) {
      builder.add(getAssignment(term));
    } else if (term.isExp()) {
      ExpressionKind.ExpressionType expKind = term.getExpressionKind();
      if (expKind == ExpressionKind.CONSTANT) {
        return;
      } else if (expKind == ExpressionKind.VAR) {
        Variable var = Dreal.getVariable(term.getExpression());
        builder.add(getAssignment(new DRealTerm<>(var, var.getType(), var.getType())));
      } else if (expKind == ExpressionKind.POW) {
        Expression lhs = Dreal.getFirstArgument(term.getExpression());
        recursiveAssignmentFinder(builder, new DRealTerm<>(lhs, term.getType(), lhs.getKind()));
      } else if (expKind == ExpressionKind.DIV) {
        Expression firstArg = Dreal.getFirstArgument(term.getExpression());
        Expression secondArg = Dreal.getSecondArgument(term.getExpression());
        recursiveAssignmentFinder(
            builder, new DRealTerm<>(firstArg, term.getType(), firstArg.getKind()));
        recursiveAssignmentFinder(
            builder, new DRealTerm<>(secondArg, term.getType(), secondArg.getKind()));
      } else if (expKind == ExpressionKind.ITE) {
        Formula cond = Dreal.getConditionalFormula(term.getExpression());
        Expression expThen = Dreal.getThenExpression(term.getExpression());
        Expression expElse = Dreal.getElseExpression(term.getExpression());
        recursiveAssignmentFinder(builder, new DRealTerm<>(cond, term.getType(), cond.getKind()));
        recursiveAssignmentFinder(
            builder, new DRealTerm<>(expThen, term.getType(), expThen.getKind()));
        recursiveAssignmentFinder(
            builder, new DRealTerm<>(expElse, term.getType(), expElse.getKind()));
      } else if (expKind == ExpressionKind.ADD) {
        // We have map of Expression and Double. Expression is the variable and Double the
        // constant of the addition. (2*x + 3*y) We can ignore the double value and only
        // recursively call the assignment finder. If we have constant in addition, we ignore the
        // constant as well (not a call to get the constant, get_constant_in_addition(Expression
        // exp))
        ExpressionDoubleMap map = Dreal.getExprToCoeffMapInAddition(term.getExpression());
        for (Expression key : map.keySet()) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(key, term.getType(), key.getKind()));
        }
      } else if (expKind == ExpressionKind.MUL) {
        // We get a map of Expression and Expression with the second Expression being the
        // exponent of the Variable. The exponent is ignored. The constant is ignored, no call
        // get_constant_in_multiplication
        ExpressionExpressionMap map =
            Dreal.getBaseToExponentMapInMultiplication(term.getExpression());
        for (Expression key : map.keySet()) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(key, term.getType(), key.getKind()));
        }
      } else {
        throw new IllegalArgumentException("Failure visiting the Term " + term + ".");
      }
    } else {
      FormulaKind.FormulaType fKind = term.getFormulaKind();
      if (fKind == FormulaKind.VAR) {
        Variable var = Dreal.getVariable(term.getFormula());
        builder.add(getAssignment(new DRealTerm<>(var, var.getType(), var.getType())));
      } else if (fKind == FormulaKind.TRUE || fKind == FormulaKind.FALSE) {
        return;
      } else if (fKind == FormulaKind.NOT) {
        Formula fNot = Dreal.getOperand(term.getFormula());
        recursiveAssignmentFinder(builder, new DRealTerm<>(fNot, term.getType(), fNot.getKind()));
      } else if (fKind == FormulaKind.EQ
          || fKind == FormulaKind.GT
          || fKind == FormulaKind.GEQ
          || fKind == FormulaKind.LT
          || fKind == FormulaKind.LEQ
          || fKind == FormulaKind.NEQ) {
        Expression leftChild = Dreal.getLhsExpression(term.getFormula());
        Expression rightChild = Dreal.getRhsExpression(term.getFormula());
        Variable.Type.Kind type;
        DReal4FormulaCreator myCreator = (DReal4FormulaCreator) creator;
        type = myCreator.getTypeForExpressions(leftChild);
        // if type is null, we did not find a variable in left child, we can ignore the formula,
        // else both child could have variable
        if (type == null) {
          type = myCreator.getTypeForExpressions(rightChild);
          recursiveAssignmentFinder(
              builder, new DRealTerm<>(rightChild, type, rightChild.getKind()));
        } else {
          recursiveAssignmentFinder(builder, new DRealTerm<>(leftChild, type, leftChild.getKind()));
          recursiveAssignmentFinder(
              builder, new DRealTerm<>(rightChild, type, rightChild.getKind()));
        }
      } else if (fKind == FormulaKind.AND || fKind == FormulaKind.OR) {
        FormulaSet fSet = Dreal.getOperands(term.getFormula());
        for (Formula f : fSet) {
          recursiveAssignmentFinder(builder, new DRealTerm<>(f, term.getType(), f.getKind()));
        }
      } else {
        // We only go through the bound variables, because we have a quantified formula
        VariableSet varSet = term.getFormula().getQuantifiedVariables();
        for (Variable var : varSet) {
          builder.add(getAssignment(new DRealTerm<>(var, var.getType(), var.getType())));
        }
      }
    }
  }

  private ValueAssignment getAssignment(DRealTerm<?, ?> term) {
    // term should be a variable
    Preconditions.checkState(term.isVar());
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    // valueTerm can be Formula or Expression
    DRealTerm<?, ?> valueTerm = evalImpl(term);
    org.sosy_lab.java_smt.api.Formula keyFormula = formulaCreator.encapsulateWithTypeOf(term);
    org.sosy_lab.java_smt.api.Formula valueFormula =
        formulaCreator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation;
    if (valueTerm.isExp()) {
      equation =
          creator.encapsulateBoolean(
              new DRealTerm<>(
                  new Formula(
                      Dreal.equal(new Expression(term.getVariable()), valueTerm.getExpression())),
                  Variable.Type.BOOLEAN,
                  FormulaKind.EQ));
    } else if (valueTerm.isFormula()) {
      equation =
          creator.encapsulateBoolean(
              new DRealTerm<>(
                  new Formula(Dreal.equal(term.getVariable(), valueTerm.getFormula())),
                  Variable.Type.BOOLEAN,
                  FormulaKind.EQ));
    } else {
      throw new UnsupportedOperationException(
          "Trying to get an Assignment from an Expression " + term + ".");
    }
    Object value = formulaCreator.convertValue(valueTerm);
    return new ValueAssignment(
        keyFormula,
        valueFormula,
        equation,
        term.getVariable().getName(),
        value,
        argumentInterpretationBuilder.build());
  }
}
