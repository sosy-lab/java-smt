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
import org.sosy_lab.java_smt.api.Model;

class StatisticsModel extends StatisticsEvaluator implements Model {

  private final Model delegate;
  private final SolverStatistics stats;

  StatisticsModel(Model pDelegate, SolverStatistics pStats) {
    super(pDelegate, pStats);
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    stats.modelListings.getAndIncrement();
    return delegate.asList();
  }
}
