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
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;


public class DReal4Model extends AbstractModel<DRealTerm<?, ?>, Type, Context> {

  private final Box model;
  private final DReal4FormulaCreator formulaCreator;
  private final DReal4TheoremProver prover;

  DReal4Model(DReal4TheoremProver prover, DReal4FormulaCreator pCreator, Box model) {
    super(prover, pCreator);
    this.model = model;
    this.prover = prover;
    this.formulaCreator = pCreator;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return null;
  }

  @Override
  protected @Nullable DRealTerm<?, ?> evalImpl(DRealTerm<?, ?> formula) {
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
        if (variable.get_type() == Type.BOOLEAN) {
          if (res > 0 ) {
            return new DRealTerm<>(Formula.True(), formula.getType(), FormulaKind.True);
          } else {
            return new DRealTerm<>(Formula.False(), formula.getType(), FormulaKind.False);
          }
        } else {
          return new DRealTerm<>(new Expression(res), formula.getType(), ExpressionKind.Constant);
        }
      }
    } else if (formula.isExp()) {
      // this will return the constant of the Expression -> if expression is (x + 1) and x
      // evaluates to 5, it will return 6 and not (5+1)
      Expression exp = formula.getExpression();
      // if expression is already a constang, just return it
      if (exp.get_kind() == ExpressionKind.Constant) {
        return new DRealTerm<>(exp, formula.getType(), ExpressionKind.Constant);
      }
      HashMap<Variable, Double> result = extractResults();
      Variables vars = exp.GetVariables();
      //TODO: to use the same extractResults()-function to extract the result of the whole formula
      // is not a "good" solution, but it works, because dReal just does nothing when
      // substituting a variable that is not in an expression
      for (Map.Entry<Variable, Double> entry : result.entrySet()) {
        Variable var = entry.getKey();
        // if we find a variable that is set in the model, but not in the Expression, abort?
        if (!vars.include(var)) {
          return null;
        }
        Double res = entry.getValue();
        if (res.isNaN()) {
          // When is result "EMPTY"?
          return null;
        } else {
          // TODO: Is it possible to get an Expression with BooleanType?
          Preconditions.checkState(formula.getType() != Type.BOOLEAN);
          exp = exp.Substitute(var, new Expression(res));
        }
      }
      return new DRealTerm<>(exp, formula.getType(), formula.getExpressionKind());
    } else {
      // this will always return a True formula
      Formula f = formula.getFormula();
      // if formula is already true or false, just return the formula
      if (f.get_kind() == FormulaKind.True || f.get_kind() == FormulaKind.False) {
        return new DRealTerm<>(f, formula.getType(), f.get_kind());
      }
      //TODO: How can I get all the Variables in a quantified Formula, is it needed?
      Variables vars = f.GetFreeVariables();
      HashMap<Variable, Double> result = extractResults();
      for (Map.Entry<Variable, Double> entry : result.entrySet()) {
        Variable var = entry.getKey();
        Double res = entry.getValue();
        // if we find a variable that is set in the model, but not in the Expression, abort?
        if (!vars.include(var)) {
          return null;
        }
        if (res.isNaN()) {
          // When is result "EMPTY"?
          return null;
        } else {
          if (var.get_type() == Type.BOOLEAN) {
            if (res > 0) {
              f = f.Substitute(var, Formula.True());
            } else {
              f = f.Substitute(var, Formula.False());
            }
          } else {
            f = f.Substitute(var, new Expression(res));
          }
        }
      }
      return new DRealTerm<>(f, formula.getType(), formula.getFormulaKind());
    }
  }

  /**
   * This function extracts the results of a formula. The function iterates through the model
   * (Box) and gets the variable and calls getResult to get the value associated with the variable
   * @return HashMap with variable as key and result as Double as value
   */
  private HashMap<Variable, Double> extractResults() {
    HashMap<Variable, Double> result = new HashMap<>();
    Variable var;
    String res;
    for (int i = 0; i < model.size(); i++) {
      var = model.variable(i);
      res = dreal.getResult(model, var);
      result.put(var, parseResult(res));
    }
    return result;
  }

  private Double extractResultsVariable(Variable var) {
    return parseResult(dreal.getResult(model, var));
  }

  private Double parseResult(String string) {
    if (string.equals("EMPTY")) {
      return Double.NaN;
    } else if (string.equals("ENTIRE")) {
      // probably unnecassary, and what should I return?
      return new Double(1);
    } else {
      String[] numbers = string.split(",");
      return new Double(numbers[0] + "." + numbers[1]);

    }
  }
}