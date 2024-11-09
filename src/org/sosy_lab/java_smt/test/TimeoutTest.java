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
import java.util.ArrayList;
import java.util.List;
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
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/** Check that timeout is handled gracefully. */
@RunWith(Parameterized.class)
public class TimeoutTest extends SolverBasedTest0 {

  private static final int TIMOUT_MILLISECONDS = 10000;

  private static final int[] DELAYS = {1, 5, 10, 20, 50, 100};

  @Parameters(name = "{0} with delay {1}")
  public static List<Object[]> getAllSolversAndDelays() {
    List<Object[]> lst = new ArrayList<>();
    for (Solvers solver : ParameterizedSolverBasedTest0.getAllSolvers()) {
      for (int delay : DELAYS) {
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

  @Test(timeout = TIMOUT_MILLISECONDS)
  public void testProverTimeoutInt() throws InterruptedException, SolverException {
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC5);
    testBasicProverTimeoutInt(() -> context.newProverEnvironment());
  }

  @Test(timeout = TIMOUT_MILLISECONDS)
  public void testProverTimeoutBv() throws InterruptedException, SolverException {
    requireBitvectors();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.CVC5);
    testBasicProverTimeoutBv(() -> context.newProverEnvironment());
  }

  @Test(timeout = TIMOUT_MILLISECONDS)
  public void testInterpolationProverTimeout() throws InterruptedException, SolverException {
    requireInterpolation();
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC5);
    testBasicProverTimeoutInt(() -> context.newProverEnvironmentWithInterpolation());
  }

  @Test(timeout = TIMOUT_MILLISECONDS)
  public void testOptimizationProverTimeout() throws InterruptedException, SolverException {
    requireOptimization();
    requireIntegers();
    testBasicProverTimeoutInt(() -> context.newOptimizationProverEnvironment());
  }

  private void testBasicProverTimeoutInt(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException, SolverException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    testBasicProverTimeout(proverConstructor, gen.generate(100));
  }

  private void testBasicProverTimeoutBv(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException, SolverException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    testBasicProverTimeout(proverConstructor, gen.generate(100));
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicProverTimeout(
      Supplier<BasicProverEnvironment<?>> proverConstructor, BooleanFormula instance)
      throws InterruptedException, SolverException {
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
}
