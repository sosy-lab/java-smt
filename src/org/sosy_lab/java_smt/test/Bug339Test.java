// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class Bug339Test extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  private final ExecutorService executor = Executors.newSingleThreadExecutor();

  @Test
  public void brokenTest() throws InterruptedException, ExecutionException {
    assume().that(solverToUse()).isEqualTo(Solvers.MATHSAT5);

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula formula = gen.generate(8);

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      prover.push(formula);

      Future<?> task1 =
          executor.submit(
              () -> {
                try {
                  // FIXME: Exception for MathSAT (bug #339)
                  // java.lang.StackOverflowError
                  //   at org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_solve
                  //       (Native Method)
                  //   at org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat
                  //       (Mathsat5NativeApi.java:156)
                  //   at org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5AbstractProver.isUnsat
                  //       (Mathsat5AbstractProver.java:106)
                  //   at org.sosy_lab.java_smt.test.ProverEnvironmentSubject.isUnsatisfiable
                  //       (ProverEnvironmentSubject.java:67)
                  //   at ..
                  assertThat(prover).isUnsatisfiable();

                } catch (SolverException | InterruptedException pE) {
                  throw new RuntimeException(pE);
                }
              });

      assert task1.get() == null;
    }
  }

  @Test
  public void fixedTest() throws InterruptedException, ExecutionException {
    // Create the ProverEnvironment on the thread that uses it
    assume().that(solverToUse()).isEqualTo(Solvers.MATHSAT5);

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula formula = gen.generate(8);

    Future<?> task1 =
        executor.submit(
            () -> {
              try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
                prover.push(formula);
                assertThat(prover).isUnsatisfiable();
              } catch (SolverException | InterruptedException pE) {
                throw new RuntimeException(pE);
              }
            });

    assert task1.get() == null;
  }
}
