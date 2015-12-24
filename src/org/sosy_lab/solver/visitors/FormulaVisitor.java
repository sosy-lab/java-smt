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

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.UfDeclaration;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

/**
 * Visitor iterating through entire formula.
 */
public abstract class FormulaVisitor<R> {
  private final FormulaManager fmgr;

  protected FormulaVisitor(FormulaManager pFmgr) {
    fmgr = pFmgr;
  }

  public R visit(Formula f) {
    return fmgr.visit(this, f);
  }

  public abstract R visitFreeVariable(Formula f, String name);

  public abstract R visitBoundVariable(Formula f, String name);

  /**
   * Visit a constant, such as "true"/"false" or a numeric constant like "1" or "1.0".
   * @param value The value of the constant. It is either of type {@link Boolean} or of a subtype
   *     of {@link Number}, in most cases a {@link BigInteger}, {@link BigDecimal},
   *     or {@link Rational}.
   * @param type The formula type of the constant.
   * @return An arbitrary return value that is be passed to the caller.
   */
  public abstract R visitConstant(Object value, FormulaType<?> type);

  public abstract R visitUF(Formula f, List<Formula> args, String functionName);

  public abstract R visitOperator(
      Formula f,
      List<Formula> args,
      String functionName,
      Function<List<Formula>, Formula> newApplicationConstructor);

  public abstract R visitForAll(List<Formula> bound, BooleanFormula body);

  public abstract R visitExists(List<Formula> bound, BooleanFormula body);
}
