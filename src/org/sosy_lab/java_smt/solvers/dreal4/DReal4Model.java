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
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
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

  // This will always return True, different solution?
  @Override
  protected @Nullable DRealTerm<?, ?> evalImpl(DRealTerm<?, ?> formula) {
    Preconditions.checkState(formula.isFormula());
    Formula f = formula.getFormula();
    HashMap<Variable, Double> result = extractResults();
    for (Map.Entry<Variable, Double> entry : result.entrySet()) {
      Variable var = entry.getKey();
      Double res = entry.getValue();
      if (res.isNaN()) {
        // When is result "EMPTY"?
        return null;
      } else {
        if (var.get_type() == Type.BOOLEAN) {
          if (res > 0) {
            f.Substitute(var, Formula.True());
          } else {
            f.Substitute(var, Formula.False());
          }
        } else {
          f.Substitute(var, new Expression(res));
        }
      }
    }
    return new DRealTerm<>(f, formula.getType(), formula.getFormulaKind());
  }


  /**
   * This function extracts the results. The function iterates through the model (Box) and gets the
   * variable and calls getResult to get the value associated with the variable
   * @return HashMap with variable as key and result as Double as value
   */
  private HashMap<Variable, Double> extractResults() {
    HashMap<Variable, Double> result = new HashMap<>();
    Variable var;
    String res;
    for (int i = 0; i < model.size(); i++) {
      var = model.variable(i);
      res = dreal.getResult(model, i);
      result.put(var, parseResult(res));
    }
    return result;
  }

  private double parseResult(String string) {
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