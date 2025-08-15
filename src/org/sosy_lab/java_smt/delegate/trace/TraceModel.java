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

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;

public class TraceModel implements Model {
  private final Model delegate;
  private final TraceLogger logger;

  TraceModel(Model pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    // FIXME We need to introduce local variables for all terms in the model so that they can be
    //  referenced later
    return logger.logDef(logger.toVariable(this), "asList()", delegate::asList);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("eval(%s)", logger.toVariable(formula)),
        () -> delegate.eval(formula));
  }

  @Override
  public @Nullable Object evaluate(Formula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable String evaluate(StringFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula) {
    return logger.logDef(
        logger.toVariable(this),
        String.format("evaluate(%s)", logger.toVariable(formula)),
        () -> delegate.evaluate(formula));
  }

  @Override
  public void close() {
    logger.logStmt(logger.toVariable(this), "close()", delegate::close);
  }
}
