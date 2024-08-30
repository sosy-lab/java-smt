// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/**
 * Interface which operates over {@link IntegerFormula}s.
 *
 * <p>Integer formulas always take integral formulas as arguments.
 */
public interface IntegerFormulaManager
    extends NumeralFormulaManager<IntegerFormula, IntegerFormula> {

  /** Create a term representing the constraint {@code number1 == number2 (mod n)}. */
  BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, BigInteger n);

  /** Create a term representing the constraint {@code number1 == number2 (mod n)}. */
  BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n);

  /**
   * Create a formula representing the modulo of two operands according to Boute's Euclidean
   * definition.
   *
   * <p>If the denominator evaluates to zero (modulo-by-zero), either directly as value or
   * indirectly via an additional constraint, then the solver is allowed to choose an arbitrary
   * value for the result of the modulo operation (cf. SMTLIB standard for the division operator in
   * Ints or Reals theory).
   *
   * <p>Examples:
   *
   * <ul>
   *   <li>10 % 5 == 0
   *   <li>10 % 3 == 1
   *   <li>10 % (-3) == 1
   *   <li>-10 % 5 == 0
   *   <li>-10 % 3 == 2
   *   <li>-10 % (-3) == 2
   * </ul>
   *
   * <p>Note: Some solvers, e.g., Yices2, abort with an exception when exploring a modulo-by-zero
   * during the SAT-check. This is not compliant to the SMTLIB standard, but sadly happens.
   */
  IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator);

  @Override
  default FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
