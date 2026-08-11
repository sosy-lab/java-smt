/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.delegate;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

@SuppressWarnings("unused")
public class SynchronizedTest extends SolverBasedTest0 {
  @Override
  protected ConfigurationBuilder createTestConfigBuilder() throws InvalidConfigurationException {
    return super.createTestConfigBuilder()
        .setOption("solver.synchronize", "true")
        .setOption("solver.synchronized.useSeperateProvers", "true");
  }

  @Test
  public void booleanEvalTest() throws SolverException, InterruptedException {
    try (ProverEnvironment prover =
        context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      BooleanFormula a = bmgr.makeVariable("A");
      BooleanFormula b = bmgr.makeVariable("B");
      prover.addConstraint(bmgr.not(a));

      var unused = prover.isUnsat();

      try (Evaluator evaluator = prover.getEvaluator()) {
        assertThat(evaluator.eval(bmgr.and(a, b))).isEqualTo(bmgr.makeFalse());
      }
    }
  }

  @Test
  public void integerEvalTest() throws SolverException, InterruptedException {
    try (ProverEnvironment prover =
        context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      NumeralFormula.IntegerFormula variable = imgr.makeVariable("a");
      NumeralFormula.IntegerFormula zero = imgr.makeNumber(0);
      prover.addConstraint(imgr.equal(variable, zero));

      var unused = prover.isUnsat();

      try (Evaluator evaluator = prover.getEvaluator()) {
        assertThrows(UnsupportedOperationException.class, () -> evaluator.eval(variable));
      }
    }
  }
}
