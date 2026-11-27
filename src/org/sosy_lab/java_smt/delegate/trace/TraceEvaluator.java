/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.StringFormula;

public class TraceEvaluator implements Evaluator {
  private final Evaluator delegate;

  private final TraceFormulaManager mgr;
  private final TraceLogger logger;

  TraceEvaluator(Evaluator pDelegate, TraceFormulaManager pMgr, TraceLogger pLogger) {
    delegate = pDelegate;
    mgr = pMgr;
    logger = pLogger;
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula) {
    var value =
        logger.logDefDiscard(
            logger.toVariable(this),
            "eval(%s)".formatted(logger.toVariable(formula)),
            () -> delegate.eval(formula));
    return value == null ? null : mgr.rebuild(value);
  }

  @Override
  public @Nullable Object evaluate(Formula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable BigInteger evaluate(NumeralFormula.IntegerFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable Rational evaluate(NumeralFormula.RationalFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable String evaluate(StringFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "evaluate(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public void close() {
    logger.logStmt(logger.toVariable(this), "close()", delegate::close);
  }
}
