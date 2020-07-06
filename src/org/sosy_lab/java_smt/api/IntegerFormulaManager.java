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

  IntegerFormula modulo(IntegerFormula number1, IntegerFormula number2);

  @Override
  default FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
