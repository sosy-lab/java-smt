// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.Iterator;
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
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

class StatisticsModel implements Model {

  private final Model delegate;
  private final SolverStatistics stats;

  StatisticsModel(Model pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T pFormula)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.eval(pFormula);
  }

  @Override
  public @Nullable Object evaluate(Formula pF) throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable String evaluate(StringFormula pF) throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula pF)
      throws InterruptedException, SolverException {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() throws InterruptedException, SolverException {
    stats.modelListings.getAndIncrement();
    return delegate.asList();
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    stats.modelListings.getAndIncrement();
    return delegate.iterator();
  }

  @Override
  public void close() {
    delegate.close();
  }
}
