// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.ProverEnvironment;

class StatisticsProverEnvironment extends StatisticsBasicProverEnvironment<Formula>
    implements ProverEnvironment {

  StatisticsProverEnvironment(BasicProverEnvironment<Formula> pDelegate, SolverStatistics pStats) {
    super(pDelegate, pStats);
  }
}
