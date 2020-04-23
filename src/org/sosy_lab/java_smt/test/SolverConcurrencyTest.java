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
import static com.google.common.truth.Truth8.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
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

@RunWith(Parameterized.class)
public class SolverConcurrencyTest {

  private static final int NUMBER_OF_THREADS = 4;
  private static final int TIMEOUT_SECONDS = 30;

  private static List<Throwable> exceptionsList;

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;


  protected Solvers solverToUse() {
    return solver;
  }

  @BeforeClass
  public static void createExceptionsList() {
    exceptionsList = Collections.synchronizedList(new ArrayList<Throwable>());
  }

  @After
  public void resetExceptionsList() {
    exceptionsList.clear();
  }

  @Test
  public void testIntConcurrencyWithConcurrentContext() {
    // Test concurrency of integers (while every thread creates its unique context on its own
    // concurrently)
    assume().withMessage("Solver %s does not support the theory of bitvectors", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
    List<Runnable> runnableList = new ArrayList<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      Runnable test = new Runnable() {
        @SuppressWarnings("resource")
        @Override
        public void run() {
          try {
            SolverContext context = initSolver();
            intConcurrencyTest(context);
            closeSolver(context);
          } catch (Throwable e) {
            exceptionsList.add(e);
          }
        }
      };
      runnableList.add(test);
    }
    assertConcurrency(runnableList, "testBasicIntConcurrency");
  }

  @Test
  public void testBvConcurrencyWithConcurrentContext() {
    // Test concurrency of bitvectors (while every thread creates its unique context on its own
    // concurrently)
    assume().withMessage("Solver %s does not support the theory of bitvectors", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.SMTINTERPOL);
    List<Runnable> runnableList = new ArrayList<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      Runnable test = new Runnable() {
        @SuppressWarnings("resource")
        @Override
        public void run() {
          try {
            SolverContext context = initSolver();
            bvConcurrencyTest(context);
            closeSolver(context);
          } catch (Throwable e) {
            exceptionsList.add(e);
          }
        }
      };
      runnableList.add(test);
    }
    assertConcurrency(runnableList, "testBasicIntConcurrency");
  }

  @SuppressWarnings("resource")
  @Test
  public void testIntConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    // Test concurrency with already present and unique context per thread
    assume().withMessage("Solver %s does not support the theory of bitvectors", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
    List<Runnable> runnableList = new ArrayList<>();
    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
      Runnable test = new Runnable() {
        @SuppressWarnings("resource")
        @Override
        public void run() {
          try {
            SolverContext context = contextList.poll();
            intConcurrencyTest(context);
            closeSolver(context);
          } catch (Throwable e) {
            exceptionsList.add(e);
          }
        }
      };
      runnableList.add(test);
    }
    assertConcurrency(runnableList, "testBasicIntConcurrency");
  }

  @SuppressWarnings("resource")
  @Test
  public void testBvConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    // Test concurrency with already present and unique context per thread
    assume().withMessage("Solver %s does not support the theory of bitvectors", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.SMTINTERPOL);
    List<Runnable> runnableList = new ArrayList<>();
    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
      Runnable test = new Runnable() {
        @SuppressWarnings("resource")
        @Override
        public void run() {
          try {
            SolverContext context = contextList.poll();
            bvConcurrencyTest(context);
            closeSolver(context);
          } catch (Throwable e) {
            exceptionsList.add(e);
          }
        }
      };
      runnableList.add(test);
    }
    assertConcurrency(runnableList, "testBasicIntConcurrency");
  }

  @Test
  public void testConcurrentOptimization() {
    assume().that(solverToUse()).isAnyOf(Solvers.Z3, Solvers.MATHSAT5);
    List<Runnable> runnableList = new ArrayList<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      Runnable test = new Runnable() {
        @SuppressWarnings("resource")
        @Override
        public void run() {
          try {
            SolverContext context = initSolver();
            optimizationTest(context);
            closeSolver(context);
          } catch (Throwable e) {
            exceptionsList.add(e);
          }
        }
      };
      runnableList.add(test);
    }
    assertConcurrency(runnableList, "testBasicIntConcurrency");
  }


  /**
   * Uses HardBitvectorFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose a appropriate number for the used solver. Make
   * sure to not call this method with a SolverContext that does not support bitvectors! (No
   * requireBitvector() because the exceptionList would collect it and throw an exception failing
   * the test!)
   *
   * @param context used context for the test-thread (Do not reuse contexts!)
   * @throws SolverException
   * @throws InterruptedException
   */
  private void bvConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    BitvectorFormulaManager bvmgr = mgr.getBitvectorFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    BooleanFormula instance = gen.generate(bitvectorFormulaGen.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertTrue("Solver %s failed a concurrency test", pe.isUnsat());
    }
  }

  /**
   * Uses HardIntegerFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose a appropriate number for the used solver. Make
   * sure to not call this method with a SolverContext that does not support integers! (No
   * requireIntegers() because the exceptionList would collect it and throw an exception failing the
   * test!)
   *
   * @param context used context for the test-thread (Do not reuse contexts unless you know what you
   *        are doing!)
   * @throws SolverException
   * @throws InterruptedException
   */
  private void intConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula instance = gen.generate(integerFormulaGen.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertTrue("Solver %s failed a concurrency test", pe.isUnsat());
    }
  }

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
   * to get more than one Context in 1 method in a controlled way)
   *
   * @return new SolverContext
   * @throws InvalidConfigurationException
   */
  private SolverContext initSolver() throws InvalidConfigurationException {
    try {
      Configuration config =
          Configuration.builder().setOption("solver.solver", solverToUse().toString()).build();
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

  // TODO: make a Collection of used contextes and end them with annotation after
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
   * @param runnableList A list of Runnable to be tested (make sure its NUMBER_OF_THREADS long for
   *        proper testing)
   * @param testName Name of the test for accurate error messages
   */
  private static void assertConcurrency(List<? extends Runnable> runnableList, String testName) {
    int numOfThreads = runnableList.size();
    final ExecutorService threadPool = Executors.newFixedThreadPool(numOfThreads);

    try {
      // Waits for all threads to be started
      final CountDownLatch allExecutorThreadsReady = new CountDownLatch(numOfThreads);
      // Syncs start of tests after all threads are already created
      final CountDownLatch afterInitBlocker = new CountDownLatch(1);
      // Syncs end of tests (And prevents Deadlocks in test-threads etc.)
      final CountDownLatch allDone = new CountDownLatch(numOfThreads);
      for (Runnable runnable : runnableList) {
        threadPool.submit(new Runnable() {
          @Override
          public void run() {
            allExecutorThreadsReady.countDown();
            try {
              afterInitBlocker.await();
              runnable.run();
            } catch (Throwable e) {
              exceptionsList.add(e);
            } finally {
              allDone.countDown();
            }
          }
        });
      }
      assertTrue(
          "Timeout initializing the Threads for " + testName,
          allExecutorThreadsReady.await(numOfThreads * 10, TimeUnit.MILLISECONDS));
      afterInitBlocker.countDown();
      assertTrue("Timeout in " + testName, allDone.await(TIMEOUT_SECONDS, TimeUnit.SECONDS));
    } catch (Throwable e) {
      exceptionsList.add(e);
    } finally {
      threadPool.shutdownNow();
    }
    assertTrue(
        "Test " + testName + " failed with exception(s): " + exceptionsList,
        exceptionsList.isEmpty());
  }

  /**
   * As some Solvers are slow... very slow.... and we don't want to wait till the heat death of the
   * universe nor a 0,1 second test for the faster ones we choose an appropriate number of formulas
   * to solve here
   */
  Map<Solvers, Integer> integerFormulaGen =
      Map.of(
          Solvers.SMTINTERPOL,
          12,
          Solvers.CVC4,
          16,
          Solvers.MATHSAT5,
          16,
          Solvers.PRINCESS,
          12,
          Solvers.Z3,
          16);

  Map<Solvers, Integer> bitvectorFormulaGen =
      Map.of(
          Solvers.BOOLECTOR,
          60,
          Solvers.CVC4,
          9,
          Solvers.MATHSAT5,
          60,
          Solvers.PRINCESS,
          9,
          Solvers.Z3,
          50);
}