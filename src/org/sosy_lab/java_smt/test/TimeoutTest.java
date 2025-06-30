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
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.BOOLECTOR;

import com.google.common.collect.ImmutableList;
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
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BasicProverEnvironment.AllSatCallback;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
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
    contextShutdownManager.requestShutdown(msg);
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

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();

    testBasicProverTimeoutBv(
        () -> context.newProverEnvironment(proverShutdownManager1.getNotifier()),
        proverShutdownManager1);
    assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
    assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isTrue();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(3));
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // Test shutdown of prover specific shutdown manager. The context should still be usable!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentNewProverUsageInt()
      throws InterruptedException, SolverException {
    requireIntegers();
    requireIsolatedProverShutdown();

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();

    testBasicProverTimeoutInt(
        () -> context.newProverEnvironment(proverShutdownManager1.getNotifier()),
        proverShutdownManager1);
    assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
    assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isTrue();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(3));
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // TODO: add model evaluation interrupt test for context and prover interrupt

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentNewProverUsageBv() throws InterruptedException {
    requireBitvectors();

    testBasicContextTimeoutBv(() -> context.newProverEnvironment());
    assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      assertThrows(InterruptedException.class, () -> pe.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentNewProverUsageInt() throws InterruptedException {
    requireIntegers();

    testBasicContextTimeoutInt(() -> context.newProverEnvironment());
    assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();

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

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  // This test re-uses provers that already existed before the shutdown.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentProverUsageBv() throws InterruptedException {
    requireBitvectors();
    assume()
        .withMessage("Boolector does not support multiple provers")
        .that(solverToUse())
        .isNotEqualTo(BOOLECTOR);

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment()) {
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment()) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutBv(() -> context.newProverEnvironment());
        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();

        assertThrows(InterruptedException.class, () -> pe2.push(gen.generate(8)));
        assertThrows(InterruptedException.class, pe2::isUnsat);
      }
      assertThrows(InterruptedException.class, () -> pe1.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe1::isUnsat);
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  // This test re-uses provers that already existed before the shutdown.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentProverUsageInt() throws InterruptedException {
    requireIntegers();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment()) {
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment()) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutInt(() -> context.newProverEnvironment());
        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();

        assertThrows(InterruptedException.class, () -> pe2.push(gen.generate(8)));
        assertThrows(InterruptedException.class, pe2::isUnsat);
      }
      assertThrows(InterruptedException.class, () -> pe1.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe1::isUnsat);
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  // This test re-uses provers that already existed before the shutdown with their own prover
  // based shutdown notifiers that have not been triggered.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentProverWithNotifierUsageBv()
      throws InterruptedException {
    requireBitvectors();
    assume()
        .withMessage("Boolector does not support multiple provers")
        .that(solverToUse())
        .isNotEqualTo(BOOLECTOR);
    requireIsolatedProverShutdown();

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();
    ShutdownManager proverShutdownManager2 = ShutdownManager.create();
    ShutdownManager proverShutdownManager3 = ShutdownManager.create();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe1 =
        context.newProverEnvironment(proverShutdownManager1.getNotifier())) {
      try (BasicProverEnvironment<?> pe2 =
          context.newProverEnvironment(proverShutdownManager2.getNotifier())) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutBv(
            () -> context.newProverEnvironment(proverShutdownManager3.getNotifier()));
        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isFalse();

        assertThrows(InterruptedException.class, () -> pe2.push(gen.generate(8)));
        assertThrows(InterruptedException.class, pe2::isUnsat);
      }
      assertThrows(InterruptedException.class, () -> pe1.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe1::isUnsat);
    }
  }

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  // This test re-uses provers that already existed before the shutdown with their own prover
  // based shutdown notifiers that have not been triggered.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentProverWithNotifierUsageInt()
      throws InterruptedException {
    requireIntegers();
    requireIsolatedProverShutdown();

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();
    ShutdownManager proverShutdownManager2 = ShutdownManager.create();
    ShutdownManager proverShutdownManager3 = ShutdownManager.create();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe1 =
        context.newProverEnvironment(proverShutdownManager1.getNotifier())) {
      try (BasicProverEnvironment<?> pe2 =
          context.newProverEnvironment(proverShutdownManager2.getNotifier())) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutInt(
            () -> context.newProverEnvironment(proverShutdownManager3.getNotifier()));
        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isFalse();

        assertThrows(InterruptedException.class, () -> pe2.push(gen.generate(8)));
        assertThrows(InterruptedException.class, pe2::isUnsat);
      }
      assertThrows(InterruptedException.class, () -> pe1.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe1::isUnsat);
    }
  }

  // Test shutdown of prover and subsequent feature usage.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentFeatureUsageBv()
      throws InterruptedException, SolverException {
    requireBitvectors();
    requireIsolatedProverShutdown();

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();
    ShutdownManager proverShutdownManager2 = ShutdownManager.create();
    ShutdownManager proverShutdownManager3 = ShutdownManager.create();
    ShutdownManager proverShutdownManager4 = ShutdownManager.create();

    try (BasicProverEnvironment<?> pe1 =
        context.newProverEnvironment(
            proverShutdownManager1.getNotifier(),
            ProverOptions.GENERATE_UNSAT_CORE,
            ProverOptions.GENERATE_MODELS,
            ProverOptions.GENERATE_ALL_SAT,
            ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      assertProverAPIUsable(pe1);
      try (BasicProverEnvironment<?> pe2 =
          context.newProverEnvironment(
              proverShutdownManager2.getNotifier(),
              ProverOptions.GENERATE_UNSAT_CORE,
              ProverOptions.GENERATE_MODELS,
              ProverOptions.GENERATE_ALL_SAT,
              ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
        assertProverAPIUsable(pe2);

        testBasicProverTimeoutWithFeatureUsageBv(
            () ->
                context.newProverEnvironment(
                    proverShutdownManager3.getNotifier(),
                    ProverOptions.GENERATE_UNSAT_CORE,
                    ProverOptions.GENERATE_MODELS,
                    ProverOptions.GENERATE_ALL_SAT,
                    ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS),
            proverShutdownManager3);

        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager4.getNotifier().shouldShutdown()).isFalse();

        boolean notifier4Shutdown = true;

        try {
          testBasicProverTimeoutWithFeatureUsageBv(
              () ->
                  context.newProverEnvironmentWithInterpolation(
                      proverShutdownManager4.getNotifier(),
                      ProverOptions.GENERATE_UNSAT_CORE,
                      ProverOptions.GENERATE_MODELS,
                      ProverOptions.GENERATE_ALL_SAT,
                      ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS),
              proverShutdownManager4);
        } catch (UnsupportedOperationException ignore) {
          // Do nothing, not supported
          notifier4Shutdown = false;
        }

        // TODO: optimization (or prover gen as test param?)

        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager4.getNotifier().shouldShutdown())
            .isEqualTo(notifier4Shutdown);

        assertProverAPIUsable(pe2);
      }
      assertProverAPIUsable(pe1);
    }
  }

  // Test shutdown of prover and subsequent feature usage.
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentFeatureUsageInt()
      throws InterruptedException, SolverException {
    requireIntegers();
    requireIsolatedProverShutdown();

    ShutdownManager proverShutdownManager1 = ShutdownManager.create();
    ShutdownManager proverShutdownManager2 = ShutdownManager.create();
    ShutdownManager proverShutdownManager3 = ShutdownManager.create();
    ShutdownManager proverShutdownManager4 = ShutdownManager.create();

    try (BasicProverEnvironment<?> pe1 =
        context.newProverEnvironment(
            proverShutdownManager1.getNotifier(),
            ProverOptions.GENERATE_UNSAT_CORE,
            ProverOptions.GENERATE_MODELS,
            ProverOptions.GENERATE_ALL_SAT,
            ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {

      assertProverAPIUsable(pe1);

      try (BasicProverEnvironment<?> pe2 =
          context.newProverEnvironment(
              proverShutdownManager2.getNotifier(),
              ProverOptions.GENERATE_UNSAT_CORE,
              ProverOptions.GENERATE_MODELS,
              ProverOptions.GENERATE_ALL_SAT,
              ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
        assertProverAPIUsable(pe2);

        // Test Shutdown of prover with notifier proverShutdownManager3
        testBasicProverTimeoutWithFeatureUsageInt(
            () ->
                context.newProverEnvironment(
                    proverShutdownManager3.getNotifier(),
                    ProverOptions.GENERATE_UNSAT_CORE,
                    ProverOptions.GENERATE_MODELS,
                    ProverOptions.GENERATE_ALL_SAT,
                    ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS),
            proverShutdownManager3);

        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager4.getNotifier().shouldShutdown()).isFalse();

        boolean notifier4Shutdown = true;

        try {
          testBasicProverTimeoutWithFeatureUsageInt(
              () ->
                  context.newProverEnvironmentWithInterpolation(
                      proverShutdownManager4.getNotifier(),
                      ProverOptions.GENERATE_UNSAT_CORE,
                      ProverOptions.GENERATE_MODELS,
                      ProverOptions.GENERATE_ALL_SAT,
                      ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS),
              proverShutdownManager4);
        } catch (UnsupportedOperationException ignore) {
          // Do nothing, not supported
          notifier4Shutdown = false;
        }

        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager4.getNotifier().shouldShutdown())
            .isEqualTo(notifier4Shutdown);

        // TODO: optimization (or prover gen as test param?)

        assertThat(contextShutdownManager.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager1.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager2.getNotifier().shouldShutdown()).isFalse();
        assertThat(proverShutdownManager3.getNotifier().shouldShutdown()).isTrue();
        assertThat(proverShutdownManager4.getNotifier().shouldShutdown())
            .isEqualTo(notifier4Shutdown);

        assertProverAPIUsable(pe2);
      }
      assertProverAPIUsable(pe1);
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
  private void testBasicProverTimeoutInt(
      Supplier<BasicProverEnvironment<?>> proverConstructor, ShutdownManager managerToInterrupt)
      throws InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testBasicProverBasedTimeout(proverConstructor, gen.generate(200), managerToInterrupt);
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   */
  private void testBasicProverTimeoutBv(
      Supplier<BasicProverEnvironment<?>> proverConstructor, ShutdownManager managerToInterrupt)
      throws InterruptedException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    testBasicProverBasedTimeout(proverConstructor, gen.generate(200), managerToInterrupt);
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   * Will try to use all available features of the solver afterward. (Model, UnsatCore etc.)
   */
  private void testBasicProverTimeoutWithFeatureUsageInt(
      Supplier<BasicProverEnvironment<?>> proverConstructor, ShutdownManager managerToInterrupt)
      throws InterruptedException, SolverException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testProverBasedTimeoutWithFeatures(proverConstructor, gen.generate(200), managerToInterrupt);
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   * Will try to use all available features of the solver afterward. (Model, UnsatCore etc.)
   */
  private void testBasicProverTimeoutWithFeatureUsageBv(
      Supplier<BasicProverEnvironment<?>> proverConstructor, ShutdownManager managerToInterrupt)
      throws InterruptedException, SolverException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    testProverBasedTimeoutWithFeatures(proverConstructor, gen.generate(200), managerToInterrupt);
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
                contextShutdownManager.requestShutdown("Shutdown Request");
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
      Supplier<BasicProverEnvironment<?>> proverConstructor,
      BooleanFormula instance,
      ShutdownManager managerToInterrupt)
      throws InterruptedException {

    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      Thread t =
          new Thread(
              () -> {
                try {
                  Thread.sleep(delay);
                  managerToInterrupt.requestShutdown("Shutdown Request");
                } catch (InterruptedException exception) {
                  throw new UnsupportedOperationException("Unexpected interrupt", exception);
                }
              });
      pe.push(instance);
      t.start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  /**
   * You can hand this a TheoremProver, InterpolatingProver or OptimizationProver, and it tests all
   * common features after interrupt.
   */
  private void testProverBasedTimeoutWithFeatures(
      Supplier<BasicProverEnvironment<?>> proverConstructor,
      BooleanFormula instance,
      ShutdownManager managerToInterrupt)
      throws InterruptedException, SolverException {

    // TODO: maybe add a test that solves something correctly before interrupting?

    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      Thread t =
          new Thread(
              () -> {
                try {
                  Thread.sleep(delay);
                  managerToInterrupt.requestShutdown("Shutdown Request");
                } catch (InterruptedException exception) {
                  throw new UnsupportedOperationException("Unexpected interrupt", exception);
                }
              });
      pe.push(instance);
      t.start();
      assertProverAPIThrowsInterruptedException(pe);
    }
  }

  /**
   * This always starts with isUnsat() that should be interrupted (either while solving or before).
   * The correct options for the usage of UnsatCore and UnsatCoreOverAssumptions have not to be set!
   */
  @SuppressWarnings("CheckReturnValue")
  private void assertProverAPIThrowsInterruptedException(BasicProverEnvironment<?> pe)
      throws SolverException {
    assertThrows(InterruptedException.class, pe::isUnsat);
    // TODO: let all the API in prover throw interrupted?
    assertThrows(IllegalStateException.class, pe::getModel);
    assertThrows(IllegalStateException.class, pe::getModelAssignments);
    assertThrows(IllegalStateException.class, pe::getEvaluator);
    assertThrows(IllegalStateException.class, pe::getUnsatCore);
    try {
      pe.allSat(
          new AllSatCallback<>() {

            private final List<List<BooleanFormula>> models = new ArrayList<>();

            @Override
            public void apply(List<BooleanFormula> pModel) {
              models.add(pModel);
            }

            @Override
            public List<List<BooleanFormula>> getResult() {
              return models;
            }
          },
          ImmutableList.of(bmgr.makeFalse()));
    } catch (UnsupportedOperationException ignore) {
      // Feature not supported
    } catch (InterruptedException expected) {
      assertThat(expected).isNotNull();
    }
    assertThrows(
        InterruptedException.class,
        () -> pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(
        InterruptedException.class,
        () -> pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(InterruptedException.class, () -> pe.addConstraint(bmgr.makeFalse()));

    assertThrows(InterruptedException.class, () -> pe.addConstraint(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, () -> pe.push(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, pe::push);
    assertThrows(IllegalStateException.class, pe::pop);
    if (pe instanceof InterpolatingProverEnvironment) {
      InterpolatingProverEnvironment<?> ipe = (InterpolatingProverEnvironment<?>) pe;
      assertThrows(InterruptedException.class, () -> ipe.getInterpolant(ImmutableList.of()));
      try {
        ipe.getSeqInterpolants(ImmutableList.of());
      } catch (UnsupportedOperationException ignore) {
        // Feature not supported
      } catch (InterruptedException expected) {
        assertThat(expected).isNotNull();
      }
      try {
        ipe.getSeqInterpolants0(ImmutableList.of());
      } catch (UnsupportedOperationException ignore) {
        // Feature not supported
      } catch (InterruptedException expected) {
        assertThat(expected).isNotNull();
      }
      try {
        ipe.getTreeInterpolants(ImmutableList.of(), new int[] {0});
      } catch (UnsupportedOperationException ignore) {
        // Feature not supported
      } catch (InterruptedException expected) {
        assertThat(expected).isNotNull();
      }
      try {
        ipe.getTreeInterpolants0(ImmutableList.of(), new int[] {0});
      } catch (UnsupportedOperationException ignore) {
        // Feature not supported
      } catch (InterruptedException expected) {
        assertThat(expected).isNotNull();
      }
    }
    if (pe instanceof OptimizationProverEnvironment) {
      OptimizationProverEnvironment ope = (OptimizationProverEnvironment) pe;
      assertThrows(InterruptedException.class, () -> ope.maximize(bmgr.makeFalse()));
      assertThrows(InterruptedException.class, () -> ope.minimize(bmgr.makeFalse()));
      assertThrows(InterruptedException.class, ope::check);
      assertThrows(InterruptedException.class, () -> ope.upper(1, Rational.ZERO));
      assertThrows(InterruptedException.class, () -> ope.lower(1, Rational.ZERO));
      assertThrows(InterruptedException.class, ope::getModel);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  private void assertProverAPIUsable(BasicProverEnvironment<?> pe)
      throws SolverException, InterruptedException {
    pe.addConstraint(bmgr.makeTrue());
    pe.isUnsat();
    pe.getModel().close();
    pe.getModelAssignments();
    pe.getEvaluator().close();
    try {
      pe.allSat(
          new AllSatCallback<>() {

            private final List<List<BooleanFormula>> models = new ArrayList<>();

            @Override
            public void apply(List<BooleanFormula> pModel) {
              models.add(pModel);
            }

            @Override
            public List<List<BooleanFormula>> getResult() {
              return models;
            }
          },
          ImmutableList.of(bmgr.makeTrue()));
    } catch (SolverException allowed) {
      assertThat(allowed.getMessage())
          .isEqualTo(
              "Error occurred during Mathsat allsat: allsat is "
                  + "not compatible with proof generation");
    }

    pe.push();
    pe.pop();
    pe.push(bmgr.makeFalse());
    pe.isUnsat();
    pe.getUnsatCore();

    try {
      pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.makeFalse()));
    } catch (UnsupportedOperationException ignore) {
      // Do nothing, solver does not support this feature
    }
    try {
      pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.makeFalse()));
    } catch (UnsupportedOperationException ignore) {
      // Do nothing, solver does not support this feature
    }
    pe.pop(); // Reset to SAT for repeated usage

    if (pe instanceof InterpolatingProverEnvironment) {
      InterpolatingProverEnvironment<?> ipe = (InterpolatingProverEnvironment<?>) pe;
      ipe.getInterpolant(ImmutableList.of());
      ipe.getSeqInterpolants(ImmutableList.of());
      ipe.getSeqInterpolants0(ImmutableList.of());
      ipe.getTreeInterpolants(ImmutableList.of(), new int[] {0});
      ipe.getTreeInterpolants0(ImmutableList.of(), new int[] {0});
    }
    if (pe instanceof OptimizationProverEnvironment) {
      OptimizationProverEnvironment ope = (OptimizationProverEnvironment) pe;
      ope.maximize(bmgr.makeFalse());
      ope.minimize(bmgr.makeFalse());
      ope.check();
      ope.upper(1, Rational.ZERO);
      ope.lower(1, Rational.ZERO);
      ope.getModel().close();
    }
  }
}
