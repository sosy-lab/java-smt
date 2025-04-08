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

  enum QuantifierEliminationMethod {
    /** Use the solver's built-in quantifier elimination method. */
    NATIVE,

    /** Use the solver's built-in quantifier elimination method. */
    NATIVE_FALLBACK_ON_FAILURE,

    /** Use the solver's built-in quantifier elimination method. */
    NATIVE_FALLBACK_WITH_WARNING_ON_FAILURE,

    /** Whether the solver should enable quantifier eliminiation via UltimateEliminator. */
    ULTIMATE_ELIMINATOR,

    /**
     * Whether the solver should enable quantifier eliminiation via UltimateEliminator and fall back
     * to the native quantifier elimination if UltimateEliminator's elimination method fails. The
     * solver will not log a warning in this case.
     */
    ULTIMATE_ELIMINATOR_FALLBACK_ON_FAILURE,

    /**
     * Whether the solver should enable quantifier eliminiation via UltimateEliminator and back to
     * the native quantifier elimination if UltimateEliminator's elimination method fails. The
     * solver will log a warning in this case.
     */
    ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE,
  }

  enum QuantifierCreationMethod {
    /**
     * Whether the solver should eliminate the quantifier via UltimateEliminator before inserting it
     * to the native quantified formula.
     */
    ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION,

    /**
     * Whether the solver should eliminate the quantifier via UltimateEliminator before inserting it
     * to the native quantified formula and fall back to the native quantifier creation if
     * UltimateEliminator fails. The solver will not log a warning in this case.
     */
    ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK,

    /**
     * Whether the solver should eliminate the quantifier via UltimateEliminator before inserting it
     * to the native quantified formula and fall back to the native quantifier creation if
     * UltimateEliminator fails. The solver will log a warning in this case.
     */
    ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK_WARN_ON_FAILURE
  }

  /**
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @return An existentially quantified formula.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  default BooleanFormula exists(List<? extends Formula> pVariables, BooleanFormula pBody) {
    return mkQuantifier(Quantifier.EXISTS, pVariables, pBody);
  }

  /**
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @return A universally quantified formula.
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
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @param pMethod The {@link QuantifierCreationMethod}} to decide on the creation method.
   * @return An existentially quantified formula.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  default BooleanFormula exists(
      List<? extends Formula> pVariables, BooleanFormula pBody, QuantifierCreationMethod pMethod) {
    return mkQuantifier(Quantifier.EXISTS, pVariables, pBody, pMethod);
  }

  /**
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @param pMethod The {@link QuantifierCreationMethod}} to decide on the creation method.
   * @return A universally quantified formula.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  default BooleanFormula forall(
      List<? extends Formula> pVariables, BooleanFormula pBody, QuantifierCreationMethod pMethod) {
    return mkQuantifier(Quantifier.FORALL, pVariables, pBody, pMethod);
  }

  /** Syntax sugar, see {@link #forall(List, BooleanFormula)}. */
  default BooleanFormula forall(
      Formula quantifiedArg, BooleanFormula pBody, QuantifierCreationMethod pMethod) {
    return forall(ImmutableList.of(quantifiedArg), pBody, pMethod);
  }

  /** Syntax sugar, see {@link #exists(List, BooleanFormula)}. */
  default BooleanFormula exists(
      Formula quantifiedArg, BooleanFormula pBody, QuantifierCreationMethod pMethod) {
    return exists(ImmutableList.of(quantifiedArg), pBody, pMethod);
  }

  /**
   * @param q Quantifier type
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @return A quantified formula
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * Create a formula with a specific quantifier elimination method.
   *
   * @param q Quantifier type
   * @param pVariables The variables that will get bound (variables) by the quantification.
   * @param pBody The {@link BooleanFormula}} within that the binding will be performed.
   * @param pMethod The {@link QuantifierCreationMethod}} to decide on the creation method.
   * @return A boolean formula where the quantifier may already have been eliminated.
   * @throws IllegalArgumentException If the list {@code pVariables} is empty.
   */
  BooleanFormula mkQuantifier(
      Quantifier q,
      List<? extends Formula> pVariables,
      BooleanFormula pBody,
      QuantifierCreationMethod pMethod);

  /**
   * Eliminate the quantifiers for a given formula. If this is not possible, it will return the
   * input formula. Note that CVC4 only supports this for LIA and LRA.
   *
   * @param pF Formula with quantifiers.
   * @return New formula without quantifiers.
   */
  BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException;

  /**
   * Eliminate the quantifiers for a given formula using either UltimateEliminator or the native
   * method. If this is not possible, depending on the given method it will fallback to the
   * alternative method or throw an Exception. Note that CVC4 only supports this for LIA and LRA in
   * the native elimination.
   *
   * @param pF Formula with quantifiers.
   * @param pMethod enum value for method to be used for eliminating quantifiers.
   * @return New formula without quantifiers.
   */
  BooleanFormula eliminateQuantifiers(BooleanFormula pF, QuantifierEliminationMethod pMethod)
      throws InterruptedException, SolverException;
}
