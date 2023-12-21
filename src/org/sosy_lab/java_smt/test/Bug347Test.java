// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

public class Bug347Test extends ParameterizedSolverBasedTest0 {
  private int numberOfLoops() {
    return List.of(Solvers.Z3, Solvers.PRINCESS).contains(solverToUse()) ? 10 : 100;
  }

  @SuppressWarnings("resource")
  @Test
  public void bug437BrokenTest() throws InterruptedException {
    // FIXME: Segfault for CVC5
    //  Native frames: (J=compiled Java code, j=interpreted, Vv=VM code, C=native code)
    //    C  [libcvc5.so+0x3d3eb3]  cvc5::internal::SolverEngine::~SolverEngine()+0x2d3
    //  Java frames: (J=compiled Java code, j=interpreted, Vv=VM code)
    //    j  io.github.cvc5.Solver.deletePointer(J)V+0
    //    j  io.github.cvc5.Solver.deletePointer()V+13
    //    j  org.sosy_lab.java_smt.solvers.cvc5.CVC5SolverContext.close()V+16
    //    j  org.sosy_lab.java_smt.test.Bug347Test.lambda$bug437BrokenTest$0()
    //        Ljava/lang/Object;+71
    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5);

    // FIXME: Yices2 returns sigabrt with one of these messages:
    //   "free(): corrupted unsorted chunks"
    //   "malloc_consolidate(): unaligned fastbin chunk detected"
    //   "corrupted double-linked list"
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);

    for (int k = 0; k < numberOfLoops(); k++) {
      ExecutorService exec = Executors.newFixedThreadPool(4);
      CountDownLatch barrier = new CountDownLatch(1);

      for (int i = 0; i < 4; i++) {
        @SuppressWarnings("unused")
        Future<?> future =
            exec.submit(
                () -> {
                  barrier.await();
                  SolverContext newContext = factory.generateContext();

                  FormulaManager newMgr = newContext.getFormulaManager();
                  BooleanFormulaManager newBmgr = newMgr.getBooleanFormulaManager();

                  BooleanFormula formula = newBmgr.makeFalse();

                  BasicProverEnvironment<?> prover = newContext.newProverEnvironment();
                  prover.push(formula);
                  assert prover.isUnsat();
                  prover.close();

                  newContext.close();
                  return null;
                });
      }
      exec.shutdown();

      System.out.println(k);
      barrier.countDown();

      try {
        assertWithMessage("Timeout in bug437BrokenTest")
            .that(exec.awaitTermination(10, TimeUnit.SECONDS))
            .isTrue();
      } finally {
        exec.shutdownNow();
      }
    }
  }

  @SuppressWarnings("resource")
  @Test
  public void bug437FixedTest() throws InterruptedException {
    for (int k = 0; k < numberOfLoops(); k++) {
      ExecutorService exec = Executors.newFixedThreadPool(4);
      CountDownLatch barrier = new CountDownLatch(1);

      for (int i = 0; i < 4; i++) {
        @SuppressWarnings("unused")
        Future<?> future =
            exec.submit(
                () -> {
                  barrier.await();
                  SolverContext newContext = factory.generateContext();

                  FormulaManager newMgr = newContext.getFormulaManager();
                  BooleanFormulaManager newBmgr = newMgr.getBooleanFormulaManager();

                  BooleanFormula formula = newBmgr.makeFalse();

                  BasicProverEnvironment<?> prover = newContext.newProverEnvironment();
                  prover.push(formula);
                  assertThat(prover).isUnsatisfiable();

                  return null;
                });
      }
      exec.shutdown();

      System.out.println(k);
      barrier.countDown();

      try {
        assertWithMessage("Timeout in bug437FixedTest")
            .that(exec.awaitTermination(10, TimeUnit.SECONDS))
            .isTrue();
      } finally {
        exec.shutdownNow();
      }
    }
  }
}
