// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.junit.Assert.assertThrows;

import com.google.common.truth.TruthJUnit;
import java.util.Random;
import java.util.function.Supplier;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Tactic;

/** Check that timeout is handled gracefully. */
@RunWith(Parameterized.class)
public class TimeoutTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testTacticTimeout() {
    TruthJUnit.assume()
        .withMessage("Only Z3 has native tactics")
        .that(solverToUse())
        .isEqualTo(Solvers.Z3);
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    String msg = "ShutdownRequest";
    BooleanFormula test = fuzzer.fuzz(20, 3);
    shutdownManager.requestShutdown(msg);
    assertThrows(msg, InterruptedException.class, () -> mgr.applyTactic(test, Tactic.NNF));
  }

  @Test
  public void testProverTimeoutInt() throws InterruptedException {
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.YICES2);
    testBasicProverTimeoutInt(() -> context.newProverEnvironment());
  }

  @Test
  public void testProverTimeoutBv() throws InterruptedException {
    requireBitvectors();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2);
    testBasicProverTimeoutBv(() -> context.newProverEnvironment());
  }

  @Test
  public void testInterpolationProverTimeout() throws InterruptedException {
    requireInterpolation();
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.YICES2);
    testBasicProverTimeoutInt(() -> context.newProverEnvironmentWithInterpolation());
  }

  @Test
  public void testOptimizationProverTimeout() throws InterruptedException {
    requireOptimization();
    requireIntegers();
    testBasicProverTimeoutInt(() -> context.newOptimizationProverEnvironment());
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicProverTimeoutInt(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula instance = gen.generate(20);
    Thread t =
        new Thread(
            () -> {
              try {
                Thread.sleep(1);
                shutdownManager.requestShutdown("Shutdown Request");
              } catch (InterruptedException pE) {
                throw new UnsupportedOperationException("Unexpected interrupt");
              }
            });
    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      pe.push(instance);
      t.start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicProverTimeoutBv(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    BooleanFormula instance = gen.generate(20);
    Thread t =
        new Thread(
            () -> {
              try {
                Thread.sleep(1);
                shutdownManager.requestShutdown("Shutdown Request");
              } catch (InterruptedException pE) {
                throw new UnsupportedOperationException("Unexpected interrupt");
              }
            });
    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      pe.push(instance);
      t.start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }
}
