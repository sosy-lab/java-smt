/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.visitors;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Declaration;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

public abstract class DefaultFormulaVisitor<R> implements FormulaVisitor<R> {

  /**
   * Method for default case, is called by all methods from this class if they are not overridden.
   * @param f Formula for the currently visited node.
   * @return An arbitrary value, will be passed through to the caller.
   */
  protected abstract R visitDefault(Formula f);

  @Override
  public R visitFreeVariable(Formula f, String name) {
    return visitDefault(f);
  }

  @Override
  public R visitBoundVariable(Formula f, String name, int deBruijnIdx) {
    return visitDefault(f);
  }

  @Override
  public R visitConstant(Formula f, Object value) {
    return visitDefault(f);
  }

  @Override
  public R visitFunction(
      Formula f,
      List<Formula> args,
      Declaration functionDeclaration,
      Function<List<Formula>, Formula> newApplicationConstructor) {
    return visitDefault(f);
  }

  @Override
  public R visitQuantifier(
      BooleanFormula f, Quantifier q, List<Formula> boundVariables, BooleanFormula body) {
    return visitDefault(f);
  }
}
