/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

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

public class StatisticsEvaluator implements Evaluator {

  private final Evaluator delegate;
  private final SolverStatistics stats;

  StatisticsEvaluator(Evaluator pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T pFormula) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.eval(pFormula);
  }

  @Override
  public @Nullable Object evaluate(Formula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable BigInteger evaluate(NumeralFormula.IntegerFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable Rational evaluate(NumeralFormula.RationalFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable String evaluate(StringFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public void close() {
    delegate.close();
  }
}
