// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

/**
 * This class provides methods to get concrete evaluations for formulas from the satisfiable solver
 * environment.
 *
 * <p>This class can be (but does not need to be!) a cheaper and more light-weight version of a
 * {@link Model} and it misses several features compared to a full {@link Model}:
 *
 * <ul>
 *   <li>no listing of model assignments, i.e., the user needs to query each formula on its own,
 *   <li>no guaranteed availability after applying any operation on the original prover stack, i.e.,
 *       the evaluation is only available directly after querying the solver with a satisfiable
 *       environment.
 * </ul>
 *
 * <p>If any of these features is required, please use the complete {@link Model}.
 */
public interface Evaluator extends AutoCloseable {

  /**
   * Evaluate a given formula substituting the values from the model and return it as formula.
   *
   * <p>If a value is not relevant to the satisfiability result, the solver can choose either to
   * insert an arbitrary value (e.g., the value <code>0</code> for the matching type) or just return
   * <code>null</code>.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression. The solver
   * will replace all symbols from the formula with their model values and then simplify the formula
   * into a simple formula, e.g., consisting only of a numeral expression.
   *
   * @param formula Input formula to be evaluated.
   * @return evaluation of the given formula or <code>null</code> if the solver does not provide a
   *     better evaluation.
   */
  @Nullable <T extends Formula> T eval(T formula);

  /**
   * Evaluate a given formula substituting the values from the model.
   *
   * <p>If a value is not relevant to the satisfiability result, the model can choose either an
   * arbitrary value (e.g., the value <code>0</code> for the matching type) or just return <code>
   * null</code>.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   *
   * @param formula Input formula
   * @return Either of: - Number (Rational/Double/BigInteger/Long/Integer) - Boolean
   * @throws IllegalArgumentException if a formula has unexpected type, e.g. Array.
   */
  @Nullable Object evaluate(Formula formula);

  /**
   * Type-safe evaluation for integer formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable BigInteger evaluate(IntegerFormula formula);

  /**
   * Type-safe evaluation for rational formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable Rational evaluate(RationalFormula formula);

  /**
   * Type-safe evaluation for boolean formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable Boolean evaluate(BooleanFormula formula);

  /**
   * Type-safe evaluation for bitvector formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable BigInteger evaluate(BitvectorFormula formula);

  /**
   * Type-safe evaluation for string formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable String evaluate(StringFormula formula);

  /**
   * Type-safe evaluation for enumeration formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable String evaluate(EnumerationFormula formula);

  /**
   * Type-safe evaluation for floating-point formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula);

  /**
   * Free resources associated with this evaluator (existing {@link Formula} instances stay valid,
   * but {@link #evaluate(Formula)} etc. must not be called again).
   */
  @Override
  void close();
}
