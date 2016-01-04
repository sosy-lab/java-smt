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
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

public abstract class DefaultFormulaVisitor<R> extends FormulaVisitor<R> {
  protected DefaultFormulaVisitor(FormulaManager pFmgr) {
    super(pFmgr);
  }

  protected abstract R visitDefault();

  @Override
  public R visitFreeVariable(Formula f, String name) {
    return visitDefault();
  }

  @Override
  public R visitBoundVariable(Formula f, String name, int deBruijnIdx) {
    return visitDefault();
  }

  @Override
  public R visitConstant(Formula f, Object value) {
    return visitDefault();
  }

  @Override
  public R visitFunction(
      Formula f,
      List<Formula> args,
      String functionName,
      Function<List<Formula>, Formula> newApplicationConstructor,
      boolean isUF) {
    return visitDefault();
  }

  @Override
  public R visitQuantifier(
      BooleanFormula f,
      Quantifier q,
      BooleanFormula body,
      Function<BooleanFormula, BooleanFormula> bodyTransformer) {
    return visitDefault();
  }
}
