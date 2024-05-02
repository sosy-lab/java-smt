// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class DebuggingIntegerFormulaManager
    extends DebuggingNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {
  private final IntegerFormulaManager delegate;
  private final DebuggingContext debugging;

  public DebuggingIntegerFormulaManager(
      IntegerFormulaManager pDelegate, DebuggingContext pDebugging) {
    super(pDelegate, pDebugging);
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.modularCongruence(number1, number2, n);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.modularCongruence(number1, number2, n);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denumerator) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(numerator);
    debugging.assertFormulaInContext(denumerator);
    IntegerFormula result = delegate.modulo(numerator, denumerator);
    debugging.addFormulaTerm(result);
    return result;
  }
}
