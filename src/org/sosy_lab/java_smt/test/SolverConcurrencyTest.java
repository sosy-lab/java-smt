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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.Truth8.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("resource")
@RunWith(Parameterized.class)
public class SolverConcurrencyTest {

  private static final int NUMBER_OF_THREADS = 4;
  private static final int TIMEOUT_SECONDS = 30;

  /**
   * As some Solvers are slower/faster, we choose an appropriate number of formulas to solve here.
   */
  private static final ImmutableMap<Solvers, Integer> INTEGER_FORMULA_GEN =
      ImmutableMap.of(
          Solvers.SMTINTERPOL,
          10,
          Solvers.CVC4,
          14,
          Solvers.MATHSAT5,
          16,
          Solvers.PRINCESS,
          10,
          Solvers.Z3,
          14);

  private static final ImmutableMap<Solvers, Integer> BITVECTOR_FORMULA_GEN =
      ImmutableMap.of(
          Solvers.BOOLECTOR,
          60,
          Solvers.CVC4,
          9,
          Solvers.MATHSAT5,
          60,
          Solvers.PRINCESS,
          7,
          Solvers.Z3,
          50);

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  protected Solvers solverToUse() {
    return solver;
  }

  /**
   * If UnsatisfiedLinkError (wrapped in InvalidConfigurationException) is thrown, abort the test.
   * On some systems (like Windows), some solvers are not available.
   */
  @Before
  public void checkThatSolverIsAvailable() throws InvalidConfigurationException {
    initSolver().close();
  }

  private void requireConcurrentMultipleStackSupport() {
    assume()
        .withMessage("Solver does not support concurrent solving in multiple stacks")
        .that(solver)
        .isNoneOf(
            Solvers.SMTINTERPOL, Solvers.BOOLECTOR, Solvers.MATHSAT5, Solvers.Z3, Solvers.PRINCESS);
  }

  private void requireIntegers() {
    assume()
        .withMessage("Solver does not support integers")
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  private void requireBitvectors() {
    assume()
        .withMessage("Solver does not support bitvectors")
        .that(solver)
        .isNotEqualTo(Solvers.SMTINTERPOL);
  }

  private void requireOptimization() {
    assume()
        .withMessage("Solver does not support optimization")
        .that(solver)
        .isNoneOf(Solvers.SMTINTERPOL, Solvers.BOOLECTOR, Solvers.PRINCESS, Solvers.CVC4);
  }

  /**
   * Test concurrency of integers (while every thread creates its unique context on its own
   * concurrently).
   */
  @Test
  public void testIntConcurrencyWithConcurrentContext() {
    requireIntegers();
    assertConcurrency(
        "testIntConcurrencyWithConcurrentContext",
        () -> {
          SolverContext context = initSolver();
          intConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /**
   * Test concurrency of bitvectors (while every thread creates its unique context on its own
   * concurrently).
   */
  @Test
  public void testBvConcurrencyWithConcurrentContext() {
    requireBitvectors();
    assertConcurrency(
        "testBvConcurrencyWithConcurrentContext",
        () -> {
          SolverContext context = initSolver();
          bvConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /** Test concurrency with already present and unique context per thread. */
  @SuppressWarnings("resource")
  @Test
  public void testIntConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    requireIntegers();
    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    // Initialize contexts before using them in the threads
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
    }
    assertConcurrency(
        "testIntConcurrencyWithoutConcurrentContext",
        () -> {
          SolverContext context = contextList.poll();
          intConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /** Test concurrency with already present and unique context per thread. */
  @SuppressWarnings("resource")
  @Test
  public void testBvConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    requireBitvectors();
    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    // Initialize contexts before using them in the threads
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
    }
    assertConcurrency(
        "testBvConcurrencyWithoutConcurrentContext",
        () -> {
          SolverContext context = contextList.poll();
          bvConcurrencyTest(context);
          closeSolver(context);
        });
  }

  @Test
  public void testConcurrentOptimization() {
    requireOptimization();

    assume()
        .withMessage("Solver does support optimization, but is not yet reentrant.")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    assertConcurrency(
        "testConcurrentOptimization",
        () -> {
          SolverContext context = initSolver("solver.mathsat5.loadOptimathsat5", "true");
          optimizationTest(context);
          closeSolver(context);
        });
  }

  /**
   * Test solving of large formula on concurrent stacks in one context (Stacks are not created in
   * the Threads).
   */
  @Test
  public void testConcurrentStack() throws InvalidConfigurationException, InterruptedException {
    requireConcurrentMultipleStackSupport();
    SolverContext context = initSolver();
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);

    ConcurrentLinkedQueue<BasicProverEnvironment<?>> proverList = new ConcurrentLinkedQueue<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      BooleanFormula instance = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
      BasicProverEnvironment<?> pe = context.newProverEnvironment();
      pe.push(instance);
      proverList.add(pe);
    }
    assertConcurrency(
        "testConcurrentStack",
        () -> {
          BasicProverEnvironment<?> stack = proverList.poll();
          assertWithMessage("Solver %s failed a concurrency test", solverToUse())
              .that(stack.isUnsat())
              .isTrue();
        });
    closeSolver(context);
  }

  /**
   * Uses HardBitvectorFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose a appropriate number for the used solver. Make
   * sure to not call this method with a SolverContext that does not support bitvectors! (No
   * requireBitvector() because the exceptionList would collect it and throw an exception failing
   * the test!).
   *
   * @param context used context for the test-thread (Do not reuse contexts!)
   */
  private void bvConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    BitvectorFormulaManager bvmgr = mgr.getBitvectorFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    BooleanFormula instance = gen.generate(BITVECTOR_FORMULA_GEN.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertWithMessage("Solver %s failed a concurrency test", solverToUse())
          .that(pe.isUnsat())
          .isTrue();
    }
  }

  /**
   * Uses HardIntegerFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose a appropriate number for the used solver. Make
   * sure to not call this method with a SolverContext that does not support integers! (No
   * requireIntegers() because the exceptionList would collect it and throw an exception failing the
   * test!).
   *
   * @param context used context for the test-thread (Do not reuse contexts unless you know what you
   *     are doing!)
   */
  private void intConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula instance = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertWithMessage("Solver %s failed a concurrency test", solverToUse())
          .that(pe.isUnsat())
          .isTrue();
    }
  }

  // As optimization is not used much at the moment this small test is ok
  private void optimizationTest(SolverContext context)
      throws InterruptedException, SolverException {
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");
      IntegerFormula obj = imgr.makeVariable("obj");

      prover.addConstraint(
          bmgr.and(
              imgr.lessOrEquals(x, imgr.makeNumber(10)),
              imgr.lessOrEquals(y, imgr.makeNumber(15)),
              imgr.equal(obj, imgr.add(x, y)),
              imgr.greaterOrEquals(imgr.subtract(x, y), imgr.makeNumber(1))));
      int handle = prover.maximize(obj);

      // Maximize for x.
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);

      // Check the value.
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("19"));

      try (Model model = prover.getModel()) {
        BigInteger xValue = model.evaluate(x);
        BigInteger objValue = model.evaluate(obj);
        BigInteger yValue = model.evaluate(y);

        assertThat(objValue).isEqualTo(BigInteger.valueOf(19));
        assertThat(xValue).isEqualTo(BigInteger.valueOf(10));
        assertThat(yValue).isEqualTo(BigInteger.valueOf(9));
      }
    }
  }

  /**
   * Creates and returns a completely new SolverContext for the currently used solver (We need this
   * to get more than one Context in 1 method in a controlled way).
   *
   * @param additionalOptions a list of pairs (key, value) for creating a new solver context.
   * @return new and unique SolverContext for current solver (Parameter(0))
   */
  private SolverContext initSolver(String... additionalOptions)
      throws InvalidConfigurationException {
    try {
      ConfigurationBuilder options =
          Configuration.builder().setOption("solver.solver", solverToUse().toString());
      for (int i = 0; i < additionalOptions.length; i += 2) {
        options.setOption(additionalOptions[i], additionalOptions[i + 1]);
      }
      Configuration config = options.build();
      LogManager logger = LogManager.createTestLogManager();
      ShutdownNotifier shutdownNotifier = ShutdownManager.create().getNotifier();

      SolverContextFactory factory = new SolverContextFactory(config, logger, shutdownNotifier);
      return factory.generateContext();
    } catch (InvalidConfigurationException e) {
      assume()
          .withMessage(e.getMessage())
          .that(e)
          .hasCauseThat()
          .isNotInstanceOf(UnsatisfiedLinkError.class);
      throw e;
    }
  }

  private void closeSolver(SolverContext context) {
    if (context != null) {
      context.close();
    }
  }

  /**
   * Synchronizes start and stop of a concurrency test with NUMBER_OF_THREADS threads. This method
   * will make sure that all exceptions are collected and assessed at the end, as well as stop the
   * execution after TIMEOUT_SECONDS seconds in case of a deadlock or long calculation.
   *
   * @param runnable A Runnable to be tested, make sure that it can be executed several times in
   *     parallel, i.e. no internal state except the solver itself.
   * @param testName Name of the test for accurate error messages
   */
  private static void assertConcurrency(String testName, Run runnable) {
    final ExecutorService threadPool = Executors.newFixedThreadPool(NUMBER_OF_THREADS);
    final List<Throwable> exceptionsList = Collections.synchronizedList(new ArrayList<>());

    // Waits for all threads to be started
    final CountDownLatch allExecutorThreadsReady = new CountDownLatch(NUMBER_OF_THREADS);
    // Syncs start of tests after all threads are already created
    final CountDownLatch afterInitBlocker = new CountDownLatch(1);
    // Syncs end of tests (And prevents Deadlocks in test-threads etc.)
    final CountDownLatch allDone = new CountDownLatch(NUMBER_OF_THREADS);
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      @SuppressWarnings("unused")
      Future<?> future =
          threadPool.submit(
              () -> {
                allExecutorThreadsReady.countDown();
                try {
                  afterInitBlocker.await();
                  runnable.run();
                } catch (Throwable e) {
                  exceptionsList.add(e);
                } finally {
                  allDone.countDown();
                }
              });
    }
    try {
      assertWithMessage("Timeout initializing the Threads for " + testName)
          .that(allExecutorThreadsReady.await(NUMBER_OF_THREADS * 10, TimeUnit.MILLISECONDS))
          .isTrue();
      afterInitBlocker.countDown();
      assertWithMessage("Timeout in " + testName)
          .that(allDone.await(TIMEOUT_SECONDS, TimeUnit.SECONDS))
          .isTrue();
    } catch (Throwable e) {
      exceptionsList.add(e);
    } finally {
      threadPool.shutdownNow();
    }
    assertWithMessage("Test %s failed with exception(s): %s", testName, exceptionsList)
        .that(exceptionsList.isEmpty())
        .isTrue();
  }

  /** just a small lambda-compatible interface. */
  private interface Run {
    void run() throws SolverException, InterruptedException, InvalidConfigurationException;
  }
}
