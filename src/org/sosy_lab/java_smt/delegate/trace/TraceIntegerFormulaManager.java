/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class TraceIntegerFormulaManager
    extends TraceNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {
  private final IntegerFormulaManager delegate;
  private final TraceLogger logger;

  TraceIntegerFormulaManager(IntegerFormulaManager pDelegate, TraceLogger pLogger) {
    super(pDelegate, pLogger);
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modularCongruence(%s, %s, new BigInteger(\"%s\"))",
            logger.toVariable(number1), logger.toVariable(number2), n),
        () -> delegate.modularCongruence(number1, number2, n));
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modularCongruence(%s, %s, %s)",
            logger.toVariable(number1), logger.toVariable(number2), n),
        () -> delegate.modularCongruence(number1, number2, n));
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modulo(%s, %s)", logger.toVariable(numerator), logger.toVariable(denominator)),
        () -> delegate.modulo(numerator, denominator));
  }
}
