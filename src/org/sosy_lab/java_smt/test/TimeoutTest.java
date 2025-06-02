// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/** Check that timeout is handled gracefully. */
@RunWith(Parameterized.class)
public class TimeoutTest extends SolverBasedTest0 {

  private static final int TIMEOUT_MILLISECONDS = 20000;

  private static final int[] DELAY_IN_MILLISECONDS = {5, 10, 20, 50, 100};

  @Parameters(name = "{0} with delay {1}")
  public static List<Object[]> getAllSolversAndDelays() {
    List<Object[]> lst = new ArrayList<>();
    for (Solvers solver : ParameterizedSolverBasedTest0.getAllSolvers()) {
      for (int delay : DELAY_IN_MILLISECONDS) {
        lst.add(new Object[] {solver, delay});
      }
    }
    return lst;
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public int delay;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  @Before
  public void setUp() {
    // FIXME CVC5 does not support interruption and will segfault once the timeout is reached
    //   The issue here seems to be that CVC5SolverContext.close() will free the C++ objects while
    //   the solver is still running. We could consider finding a work-around for this, or maybe
    //   ask the developers for a way to interrupt the solver.
    // TODO Add interruption for Princess
    assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.CVC5);
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testTacticTimeout() {
    assume().withMessage("Only Z3 has native tactics").that(solverToUse()).isEqualTo(Solvers.Z3);
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    String msg = "ShutdownRequest";
    BooleanFormula test = fuzzer.fuzz(20, 3);
    shutdownManager.requestShutdown(msg);
    assertThrows(msg, InterruptedException.class, () -> mgr.applyTactic(test, Tactic.NNF));
  }

  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverTimeoutInt() throws InterruptedException {
    requireIntegers();
    testBasicContextTimeoutInt(() -> context.newProverEnvironment());
  }

  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverTimeoutBv() throws InterruptedException {
    requireBitvectors();
    testBasicContextTimeoutBv(() -> context.newProverEnvironment());
  }

  // Test shutdown of prover specific shutdown manager. The context should still be usable!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentNewProverUsageBv()
      throws InterruptedException, SolverException {
    requireBitvectors();
    requireIsolatedProverShutdown();

    testBasicProverTimeoutBv(() -> context.newProverEnvironment());
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isFalse();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(8));
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // Test shutdown of prover specific shutdown manager. The context should still be usable!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentNewProverUsageInt()
      throws InterruptedException, SolverException {
    requireIntegers();
    requireIsolatedProverShutdown();

    testBasicProverTimeoutInt(() -> context.newProverEnvironment());
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isFalse();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(8));
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentNewProverUsageBv()
      throws InterruptedException, SolverException {
    requireBitvectors();
    requireIsolatedProverShutdown();

    testBasicContextTimeoutBv(() -> context.newProverEnvironment());
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(8));
      assertThrows(InterruptedException.class, pe::isUnsat);

    } catch (InterruptedException expected) {
      // We don't really know where an exception is coming from currently.
      // TODO: define where and how exceptions are thrown if we build a new prover but shutdown
      //  has been requested.
      assertThat(expected).isNotNull();
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentNewProverUsageInt()
      throws InterruptedException, SolverException {
    requireIntegers();
    requireIsolatedProverShutdown();

    testBasicContextTimeoutInt(() -> context.newProverEnvironment());
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(8));
      assertThrows(InterruptedException.class, pe::isUnsat);

    } catch (InterruptedException expected) {
      // We don't really know where an exception is coming from currently.
      // TODO: define where and how exceptions are thrown if we build a new prover but shutdown
      //  has been requested.
      assertThat(expected).isNotNull();
    }
  }

  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testInterpolationProverTimeout() throws InterruptedException {
    requireInterpolation();
    requireIntegers();
    testBasicContextTimeoutInt(() -> context.newProverEnvironmentWithInterpolation());
  }

  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testOptimizationProverTimeout() throws InterruptedException {
    requireOptimization();
    requireIntegers();
    testBasicContextTimeoutInt(() -> context.newOptimizationProverEnvironment());
  }

  /** Shuts down the shutdown manager of the context. */
  private void testBasicContextTimeoutInt(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testBasicContextBasedTimeout(proverConstructor, gen.generate(200));
  }

  /** Shuts down the shutdown manager of the context. */
  private void testBasicContextTimeoutBv(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    testBasicContextBasedTimeout(proverConstructor, gen.generate(200));
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   */
  private void testBasicProverTimeoutInt(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testBasicProverBasedTimeout(proverConstructor, gen.generate(200));
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   */
  private void testBasicProverTimeoutBv(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    testBasicProverBasedTimeout(proverConstructor, gen.generate(200));
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicContextBasedTimeout(
      Supplier<BasicProverEnvironment<?>> proverConstructor, BooleanFormula instance)
      throws InterruptedException {
    Thread t =
        new Thread(
            () -> {
              try {
                Thread.sleep(delay);
                shutdownManager.requestShutdown("Shutdown Request");
              } catch (InterruptedException exception) {
                throw new UnsupportedOperationException("Unexpected interrupt", exception);
              }
            });

    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      pe.push(instance);
      t.start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  private void testBasicProverBasedTimeout(
      Supplier<BasicProverEnvironment<?>> proverConstructor, BooleanFormula instance)
      throws InterruptedException {

    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      Thread t =
          new Thread(
              () -> {
                try {
                  Thread.sleep(delay);
                  pe.getShutdownManagerForProver().requestShutdown("Shutdown Request");
                } catch (InterruptedException exception) {
                  throw new UnsupportedOperationException("Unexpected interrupt", exception);
                }
              });
      pe.push(instance);
      t.start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }
}
