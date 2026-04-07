// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.fail;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** Regression tests for LeanSMT prover lifecycle and stack behavior. */
public class LeanSmtLifecycleTest extends SolverBasedTest0 {

  @Override
  protected Solvers solverToUse() {
    return Solvers.LEANSMT;
  }

  @Test
  public void repeatedSatChecksStayConsistentAcrossPop() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(imgr.greaterThan(x, imgr.makeNumber(0)));
      prover.push(imgr.lessThan(x, imgr.makeNumber(10)));

      assertThat(prover.isUnsat()).isFalse();
      assertThat(prover.isUnsat()).isFalse();

      prover.push(imgr.equal(x, imgr.makeNumber(0)));
      assertThat(prover.isUnsat()).isTrue();

      prover.pop();
      assertThat(prover.isUnsat()).isFalse();
      assertThat(prover.isUnsat()).isFalse();
    }
  }

  @Test
  public void assumptionsDoNotCorruptBaseSolverState() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula xEqZero = imgr.equal(x, imgr.makeNumber(0));
    BooleanFormula xEqOne = imgr.equal(x, imgr.makeNumber(1));

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(imgr.greaterThan(x, imgr.makeNumber(0)));
      prover.push(imgr.lessThan(x, imgr.makeNumber(3)));

      assertThat(prover.isUnsat()).isFalse();
      assertThrows(
          UnsupportedOperationException.class,
          () -> prover.isUnsatWithAssumptions(ImmutableList.of(xEqZero)));
      assertThrows(
          UnsupportedOperationException.class,
          () -> prover.isUnsatWithAssumptions(ImmutableList.of(xEqOne)));
      assertThat(prover.isUnsat()).isFalse();
    }
  }

  @Test(timeout = 30000)
  public void repeatedContextCreateCloseAndQuery() throws Exception {
    for (int i = 0; i < 20; i++) {
      try (SolverContext localContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdownManager.getNotifier(), Solvers.LEANSMT);
          ProverEnvironment prover = localContext.newProverEnvironment()) {

        IntegerFormula x = localContext.getFormulaManager().getIntegerFormulaManager().makeVariable("x" + i);
        BooleanFormula c =
            localContext
                .getFormulaManager()
                .getIntegerFormulaManager()
                .greaterThan(x, localContext.getFormulaManager().getIntegerFormulaManager().makeNumber(0));
        prover.push(c);
        assertThat(prover.isUnsat()).isFalse();
      }
    }
  }

  @Test(timeout = 120000)
  public void mediumEnduranceCreateCloseAndMixedQueries() throws Exception {
    for (int i = 0; i < 30; i++) {
      try (SolverContext localContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdownManager.getNotifier(), Solvers.LEANSMT);
          ProverEnvironment prover =
              localContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

        var localMgr = localContext.getFormulaManager();
        var localImgr = localMgr.getIntegerFormulaManager();
        var localRmgr = localMgr.getRationalFormulaManager();
        var localBmgr = localMgr.getBooleanFormulaManager();

        IntegerFormula x = localImgr.makeVariable("x_end_" + i);
        IntegerFormula y = localImgr.makeVariable("y_end_" + i);

        prover.push(localImgr.greaterThan(x, localImgr.makeNumber(0)));
        prover.push(localImgr.lessOrEquals(x, localImgr.makeNumber(100)));
        prover.push(localImgr.equal(y, localImgr.add(x, localImgr.makeNumber(1))));
        prover.push(localImgr.modularCongruence(y, localImgr.makeNumber(1), 1));

        var r = localRmgr.makeVariable("r_end_" + i);
        var floor = localRmgr.floor(r);
        prover.push(localRmgr.equal(r, localRmgr.makeNumber("7/3")));
        prover.push(localImgr.equal(floor, localImgr.makeNumber(2)));

        assertThat(prover.isUnsat()).isFalse();

        try (Model model = prover.getModel()) {
          assertThat(model.evaluate(localBmgr.and(localImgr.greaterThan(y, x), localImgr.equal(floor, localImgr.makeNumber(2)))))
              .isTrue();
        }
      }
    }
  }

  @Ignore(
      "LeanSMT native layer is not yet safe for bounded parallel-context stress in CI; "
          + "kept as manual investigation test.")
  @Test(timeout = 70000)
  public void concurrentIndependentContextsRemainStable() throws Exception {
    final int workers = 3;
    final int roundsPerWorker = 2;
    ExecutorService executor = Executors.newFixedThreadPool(workers);
    try {
      List<Callable<Void>> tasks = new ArrayList<>();
      for (int worker = 0; worker < workers; worker++) {
        final int workerId = worker;
        tasks.add(
            () -> {
                  for (int round = 0; round < roundsPerWorker; round++) {
                    if (Thread.currentThread().isInterrupted()) {
                      throw new InterruptedException("Worker interrupted");
                    }
                    try (SolverContext localContext =
                            SolverContextFactory.createSolverContext(
                                config, logger, shutdownManager.getNotifier(), Solvers.LEANSMT);
                        ProverEnvironment prover =
                            localContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
                      var localMgr = localContext.getFormulaManager();
                      var localImgr = localMgr.getIntegerFormulaManager();
                      var localRmgr = localMgr.getRationalFormulaManager();
                      var localBmgr = localMgr.getBooleanFormulaManager();

                      IntegerFormula x =
                          localImgr.makeVariable("x_thr_" + workerId + "_" + round);
                      IntegerFormula y =
                          localImgr.makeVariable("y_thr_" + workerId + "_" + round);
                      var r = localRmgr.makeVariable("r_thr_" + workerId + "_" + round);
                      var floor = localRmgr.floor(r);

                      prover.push(localImgr.greaterThan(x, localImgr.makeNumber(0)));
                      prover.push(localImgr.lessOrEquals(x, localImgr.makeNumber(50)));
                      prover.push(localImgr.equal(y, localImgr.add(x, localImgr.makeNumber(1))));
                      prover.push(localImgr.modularCongruence(y, localImgr.makeNumber(1), 1));
                      prover.push(localRmgr.equal(r, localRmgr.makeNumber("9/4")));
                      prover.push(localImgr.equal(floor, localImgr.makeNumber(2)));

                      assertThat(prover.isUnsat()).isFalse();

                      try (Model model = prover.getModel()) {
                        assertThat(
                                model.evaluate(
                                    localBmgr.and(
                                        localImgr.greaterThan(y, x),
                                        localImgr.equal(floor, localImgr.makeNumber(2)))))
                            .isTrue();
                      }
                    }
                  }
                  return null;
                });
      }
      List<Future<Void>> futures = executor.invokeAll(tasks, 40, TimeUnit.SECONDS);

      for (Future<Void> future : futures) {
        if (future.isCancelled()) {
          fail("Concurrent LeanSMT context test timed out");
        }
        future.get();
      }
    } finally {
      executor.shutdownNow();
      executor.awaitTermination(10, TimeUnit.SECONDS);
    }
  }

  @Test(timeout = 30000)
  public void sequentialCrossThreadContextUsageStaysStable() throws Exception {
    ExecutorService executor = Executors.newSingleThreadExecutor();
    try {
      List<Future<Void>> futures = new ArrayList<>();
      for (int i = 0; i < 6; i++) {
        final int id = i;
        futures.add(
            executor.submit(
                () -> {
                  try (SolverContext localContext =
                          SolverContextFactory.createSolverContext(
                              config, logger, shutdownManager.getNotifier(), Solvers.LEANSMT);
                      ProverEnvironment prover =
                          localContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
                    var localMgr = localContext.getFormulaManager();
                    var localImgr = localMgr.getIntegerFormulaManager();
                    IntegerFormula x = localImgr.makeVariable("x_seq_thr_" + id);
                    prover.push(localImgr.greaterThan(x, localImgr.makeNumber(0)));
                    prover.push(localImgr.lessOrEquals(x, localImgr.makeNumber(3)));
                    assertThat(prover.isUnsat()).isFalse();
                  }
                  return null;
                }));
      }
      for (Future<Void> future : futures) {
        future.get();
      }
    } finally {
      executor.shutdownNow();
      executor.awaitTermination(10, TimeUnit.SECONDS);
    }
  }

  @Test
  public void bigIntegerConstantRoundtripInModel() throws SolverException, InterruptedException {
    requireIntegers();
    requireModel();

    BigInteger big = new BigInteger("1234567890123456789012345678901234567890");
    IntegerFormula x = imgr.makeVariable("x_big");
    BooleanFormula assign = imgr.equal(x, imgr.makeNumber(big));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(assign);
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(big);
      }
    }
  }
}
