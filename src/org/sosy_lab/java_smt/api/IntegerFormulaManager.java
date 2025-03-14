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

  /**
   * Create a term representing the constraint {@code number1 == number2 (mod n)}. Note: this is not
   * formally defined by the SMTLib standard, but supported by many solvers. Please consult the
   * documentation of the used solver for details.
   */
  BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, BigInteger n);

  /**
   * Create a term representing the constraint {@code number1 == number2 (mod n)}. Note: this is not
   * formally defined by the SMTLib standard, but supported by many solvers. Please consult the
   * documentation of the used solver for details.
   */
  BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n);

  /**
   * Create a formula representing the modulo of two operands according to Boute's Euclidean
   * definition (DOI: 10.1145/128861.128862). The quotient (division of numerator by denominator) of
   * the modulo calculation (numerator - quotient * denominator = remainder, with remainder being
   * the result of this operation) is floored for positive denominators and rounded up for negative
   * denominators.
   *
   * <p>If the denominator evaluates to zero (modulo-by-zero), either directly as value or
   * indirectly via an additional constraint, then the solver is allowed to choose an arbitrary
   * value for the result of the modulo operation (cf. SMTLib standard version 2.6 for the division
   * operator in Int or Real theory). The details of this are implementation specific and may change
   * solver by solver.
   *
   * <p>Examples:
   *
   * <ul>
   *   <li>modulo(10, 5) == 0
   *   <li>modulo(10, 3) == 1
   *   <li>modulo(10, -3) == 1
   *   <li>modulo(-10, 5) == 0
   *   <li>modulo(-10, 3) == 2
   *   <li>modulo(-10, -3) == 2
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
