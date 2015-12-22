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
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.UfDeclaration;

import java.util.List;

public abstract class DefaultFormulaVisitor<R> extends FormulaVisitor<R> {
  protected DefaultFormulaVisitor(FormulaManager pFmgr) {
    super(pFmgr);
  }

  protected abstract R visitDefault();

  public R visitFreeVariable(String name, FormulaType<?> type) {
    return visitDefault();
  }

  public R visitBoundVariable(String name, FormulaType<?> type,
                                       Formula boundingAST) {
    return visitDefault();
  }

  public R visitNumeral(String numeral, FormulaType<?> type) {
    return visitDefault();
  }

  public R visitUF(
      String functionName,
      UfDeclaration<?> declaration,
      List<Formula> args) {
    return visitDefault();
  }

  public R visitFunction(
      String functionName,
      List<Formula> args,
      FormulaType<?> type,
      Function<List<Formula>, Formula> newApplicationConstructor) {
    return visitDefault();
  }

  public R visitForAll(List<Formula> variables, BooleanFormula body) {
    return visitDefault();
  }

  public R visitExists(List<Formula> variables, BooleanFormula body) {
    return visitDefault();
  }
}
