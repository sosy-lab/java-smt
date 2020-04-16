/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

class StatisticsModel implements Model {

  private final Model delegate;
  private final SolverStatistics stats;

  StatisticsModel(Model pDelegate, SolverStatistics pStats) {
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
  public @Nullable BigInteger evaluate(IntegerFormula pF) {
    stats.modelEvaluations.getAndIncrement();
    return delegate.evaluate(pF);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula pF) {
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
  public ImmutableList<ValueAssignment> asList() {
    stats.modelListings.getAndIncrement();
    return delegate.asList();
  }

  @Override
  public void close() {
    delegate.close();
  }
}
