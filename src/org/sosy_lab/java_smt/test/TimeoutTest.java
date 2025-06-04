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
import org.junit.Ignore;
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

    ShutdownManager sm1 = ShutdownManager.create();

    testBasicProverTimeoutBv(() -> context.newProverEnvironment(sm1.getNotifier()), sm1);
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isFalse();
    assertThat(sm1.getNotifier().shouldShutdown()).isTrue();

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

    ShutdownManager sm1 = ShutdownManager.create();

    testBasicProverTimeoutInt(() -> context.newProverEnvironment(sm1.getNotifier()), sm1);
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isFalse();
    assertThat(sm1.getNotifier().shouldShutdown()).isTrue();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(gen.generate(8));
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // TODO: add model evaluation interrupt test for context and prover interrupt

  // Test shutdown of context-wide shutdown manager. No prover should be usable afterward!
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentNewProverUsageBv() throws InterruptedException {
    requireBitvectors();

    testBasicContextTimeoutBv(() -> context.newProverEnvironment());
    assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

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
        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

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
        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

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

    ShutdownManager sm1 = ShutdownManager.create();
    ShutdownManager sm2 = ShutdownManager.create();
    ShutdownManager sm3 = ShutdownManager.create();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment(sm1.getNotifier())) {
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment(sm2.getNotifier())) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutBv(() -> context.newProverEnvironment(sm3.getNotifier()));
        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();
        assertThat(sm1.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm2.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm3.getNotifier().shouldShutdown()).isFalse();

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

    ShutdownManager sm1 = ShutdownManager.create();
    ShutdownManager sm2 = ShutdownManager.create();
    ShutdownManager sm3 = ShutdownManager.create();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment(sm1.getNotifier())) {
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment(sm2.getNotifier())) {
        pe2.push(gen.generate(8));

        testBasicContextTimeoutInt(() -> context.newProverEnvironment(sm3.getNotifier()));
        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();
        assertThat(sm1.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm2.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm3.getNotifier().shouldShutdown()).isFalse();

        assertThrows(InterruptedException.class, () -> pe2.push(gen.generate(8)));
        assertThrows(InterruptedException.class, pe2::isUnsat);
      }
      assertThrows(InterruptedException.class, () -> pe1.push(gen.generate(8)));
      assertThrows(InterruptedException.class, pe1::isUnsat);
    }
  }

  // Test shutdown of prover and subsequent feature usage.
  @Ignore
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testProverInterruptWithSubsequentFeatureUsageBv() throws InterruptedException {
    requireBitvectors();
    requireIsolatedProverShutdown();

    ShutdownManager sm1 = ShutdownManager.create();
    ShutdownManager sm2 = ShutdownManager.create();
    ShutdownManager sm3 = ShutdownManager.create();

    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment(sm1.getNotifier())) {
      assertProverAPIUsable(pe1);
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment(sm2.getNotifier())) {
        assertProverAPIUsable(pe2);

        testBasicProverTimeoutWithFeatureUsageBv(
            () -> context.newProverEnvironment(sm3.getNotifier()), sm3);
        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();

        assertThat(sm1.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm2.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm3.getNotifier().shouldShutdown()).isTrue();

        assertProverAPIUsable(pe2);
      }
      assertProverAPIUsable(pe1);
    }
  }

  // Test shutdown of prover and subsequent feature usage.
  @Ignore
  @Test(timeout = TIMEOUT_MILLISECONDS)
  public void testContextInterruptWithSubsequentFeatureUsageInt() throws InterruptedException {
    requireIntegers();
    requireIsolatedProverShutdown();

    ShutdownManager sm1 = ShutdownManager.create();
    ShutdownManager sm2 = ShutdownManager.create();
    ShutdownManager sm3 = ShutdownManager.create();

    try (BasicProverEnvironment<?> pe1 = context.newProverEnvironment(sm1.getNotifier())) {
      assertProverAPIUsable(pe1);
      try (BasicProverEnvironment<?> pe2 = context.newProverEnvironment(sm2.getNotifier())) {
        assertProverAPIUsable(pe2);

        testBasicProverTimeoutWithFeatureUsageInt(
            () ->
                context.newProverEnvironment(
                    sm3.getNotifier(),
                    ProverOptions.GENERATE_UNSAT_CORE,
                    ProverOptions.GENERATE_MODELS,
                    ProverOptions.GENERATE_ALL_SAT,
                    ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS),
            sm3);

        assertThat(shutdownManager.getNotifier().shouldShutdown()).isTrue();
        assertThat(sm1.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm2.getNotifier().shouldShutdown()).isFalse();
        assertThat(sm3.getNotifier().shouldShutdown()).isTrue();

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
      throws InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testProverBasedTimeoutWithFeatures(proverConstructor, gen.generate(200), managerToInterrupt);
  }

  /**
   * Shuts down the shutdown manager of the prover. Throws an exception for non-supporting solvers.
   * Will try to use all available features of the solver afterward. (Model, UnsatCore etc.)
   */
  private void testBasicProverTimeoutWithFeatureUsageBv(
      Supplier<BasicProverEnvironment<?>> proverConstructor, ShutdownManager managerToInterrupt)
      throws InterruptedException {
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
      throws InterruptedException {

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
  private void assertProverAPIThrowsInterruptedException(BasicProverEnvironment<?> pe) {
    assertThrows(InterruptedException.class, pe::isUnsat);
    assertThrows(InterruptedException.class, pe::getModel);
    assertThrows(InterruptedException.class, pe::getModelAssignments);
    assertThrows(InterruptedException.class, pe::getEvaluator);
    assertThrows(InterruptedException.class, pe::getUnsatCore);
    assertThrows(
        InterruptedException.class,
        () ->
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
                ImmutableList.of(bmgr.makeFalse())));
    assertThrows(
        InterruptedException.class,
        () -> pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(
        InterruptedException.class,
        () -> pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(InterruptedException.class, () -> pe.addConstraint(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, () -> pe.push(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, pe::push);
    assertThrows(InterruptedException.class, pe::pop);
    if (pe instanceof InterpolatingProverEnvironment) {
      InterpolatingProverEnvironment<?> ipe = (InterpolatingProverEnvironment<?>) pe;
      assertThrows(InterruptedException.class, () -> ipe.getInterpolant(ImmutableList.of()));
      assertThrows(InterruptedException.class, () -> ipe.getSeqInterpolants(ImmutableList.of()));
      assertThrows(InterruptedException.class, () -> ipe.getSeqInterpolants0(ImmutableList.of()));
      assertThrows(
          InterruptedException.class,
          () -> ipe.getTreeInterpolants(ImmutableList.of(), new int[] {0}));
      assertThrows(
          InterruptedException.class,
          () -> ipe.getTreeInterpolants0(ImmutableList.of(), new int[] {0}));
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

  private void assertProverAPIUsable(BasicProverEnvironment<?> pe) {
    assertThrows(InterruptedException.class, pe::isUnsat);
    assertThrows(InterruptedException.class, pe::getModel);
    assertThrows(InterruptedException.class, pe::getModelAssignments);
    assertThrows(InterruptedException.class, pe::getEvaluator);
    assertThrows(InterruptedException.class, pe::getUnsatCore);
    assertThrows(
        InterruptedException.class,
        () ->
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
                ImmutableList.of(bmgr.makeFalse())));
    assertThrows(
        InterruptedException.class,
        () -> pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(
        InterruptedException.class,
        () -> pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.makeFalse())));
    assertThrows(InterruptedException.class, () -> pe.addConstraint(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, () -> pe.push(bmgr.makeFalse()));
    assertThrows(InterruptedException.class, pe::push);
    assertThrows(InterruptedException.class, pe::pop);
    if (pe instanceof InterpolatingProverEnvironment) {
      InterpolatingProverEnvironment<?> ipe = (InterpolatingProverEnvironment<?>) pe;
      assertThrows(InterruptedException.class, () -> ipe.getInterpolant(ImmutableList.of()));
      assertThrows(InterruptedException.class, () -> ipe.getSeqInterpolants(ImmutableList.of()));
      assertThrows(InterruptedException.class, () -> ipe.getSeqInterpolants0(ImmutableList.of()));
      assertThrows(
          InterruptedException.class,
          () -> ipe.getTreeInterpolants(ImmutableList.of(), new int[] {0}));
      assertThrows(
          InterruptedException.class,
          () -> ipe.getTreeInterpolants0(ImmutableList.of(), new int[] {0}));
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
}
