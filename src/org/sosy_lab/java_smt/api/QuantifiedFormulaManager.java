// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableList;
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
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  default BooleanFormula exists(List<? extends Formula> pVariables, BooleanFormula pBody) {
    return mkQuantifier(Quantifier.EXISTS, pVariables, pBody);
  }

  /**
   * @return A universally quantified formula.
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  default BooleanFormula forall(List<? extends Formula> pVariables, BooleanFormula pBody) {
    return mkQuantifier(Quantifier.FORALL, pVariables, pBody);
  }

  /** Syntax sugar, see {@link #forall(List, BooleanFormula)}. */
  default BooleanFormula forall(Formula quantifiedArg, BooleanFormula pBody) {
    return forall(ImmutableList.of(quantifiedArg), pBody);
  }

  /** Syntax sugar, see {@link #exists(List, BooleanFormula)}. */
  default BooleanFormula exists(Formula quantifiedArg, BooleanFormula pBody) {
    return exists(ImmutableList.of(quantifiedArg), pBody);
  }

  /**
   * @return A quantified formula
   * @param q Quantifier type
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * Eliminate the quantifiers for a given formula. If this is not possible, it will return the
   * input formula. Note that CVC4 only supports this for LIA and LRA.
   *
   * @param pF Formula with quantifiers.
   * @return New formula without quantifiers.
   */
  BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException;
}
