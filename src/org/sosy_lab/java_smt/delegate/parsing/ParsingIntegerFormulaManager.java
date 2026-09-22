/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;

public class ParsingIntegerFormulaManager
    extends ParsingNumeralFormulaManager<
        NumeralFormula.IntegerFormula, NumeralFormula.IntegerFormula>
    implements IntegerFormulaManager {
  private final IntegerFormulaManager delegate;

  ParsingIntegerFormulaManager(
      IntegerFormulaManager pDelegate, ParsingFormulaManager.Declarations pDeclarations) {
    super(pDelegate, pDeclarations);
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula modularCongruence(
      NumeralFormula.IntegerFormula number1, NumeralFormula.IntegerFormula number2, BigInteger n) {
    return delegate.modularCongruence(number1, number2, n);
  }

  @Override
  public BooleanFormula modularCongruence(
      NumeralFormula.IntegerFormula number1, NumeralFormula.IntegerFormula number2, long n) {
    return delegate.modularCongruence(number1, number2, n);
  }

  @Override
  public NumeralFormula.IntegerFormula modulo(
      NumeralFormula.IntegerFormula numerator, NumeralFormula.IntegerFormula denominator) {
    return delegate.modulo(numerator, denominator);
  }
}
