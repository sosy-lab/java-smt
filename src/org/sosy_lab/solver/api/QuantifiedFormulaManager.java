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
package org.sosy_lab.solver.api;

import org.sosy_lab.solver.SolverException;

import java.util.List;

/**
 * This interface contains methods for working with any theory with quantifiers.
 *
 * <p>ATTENTION: Not every theory has a quantifier elimination property!
 */
public interface QuantifiedFormulaManager {

  enum Quantifier {
    FORALL,
    EXISTS
  }

  /**
   * @return An existentially quantified formula.
   *
   * @param pVariables  The variables that will get bound (variables) by the quantification.
   * @param pBody       The {@link BooleanFormula}} within that the binding will be performed.
   *
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula exists(List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * @return A universally quantified formula.
   *
   * @param pVariables  The variables that will get bound (variables) by the quantification.
   * @param pBody       The {@link BooleanFormula}} within that the binding will be performed.
   *
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula forall(List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * Syntax sugar, see {@link #forall(List, BooleanFormula)}.
   */
  BooleanFormula forall(BooleanFormula pBody, Formula... quantifiedArgs);

  /**
   * Syntax sugar, see {@link #exists(List, BooleanFormula)}.
   */
  BooleanFormula exists(BooleanFormula pBody, Formula... quantifiedArgs);

  /**
   * @return A quantified formula
   *
   * @param q           Quantifier type
   * @param pVariables  The variables that will get bound (variables) by the quantification.
   * @param pBody       The {@link BooleanFormula}} within that the binding will be performed.
   *
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * Eliminate the quantifiers for a given formula.
   *
   * @param pF Formula with quantifiers.
   * @return  New formula without quantifiers.
   */
  BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException;
}
