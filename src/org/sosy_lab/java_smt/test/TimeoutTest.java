/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

import com.google.common.truth.TruthJUnit;
import java.util.Random;
import java.util.function.Supplier;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
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

  @Rule public ExpectedException expectedEx = ExpectedException.none();

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testTacticTimeout() throws InterruptedException {
    TruthJUnit.assume()
        .withMessage("Only Z3 has native tactics")
        .that(solverToUse())
        .isEqualTo(Solvers.Z3);
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    String msg = "ShutdownRequest";
    expectedEx.expect(InterruptedException.class);
    expectedEx.expectMessage(msg);
    BooleanFormula test = fuzzer.fuzz(20, 3);
    shutdownManager.requestShutdown(msg);
    mgr.applyTactic(test, Tactic.NNF);
  }

  @Test
  public void testProverTimeoutInt() throws SolverException, InterruptedException {
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
    testBasicProverTimeoutInt(() -> context.newProverEnvironment());
  }

  @Test
  public void testProverTimeoutBv() throws SolverException, InterruptedException {
    requireBitvectors();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
    testBasicProverTimeoutBv(() -> context.newProverEnvironment());
  }

  @Test
  public void testInterpolationProverTimeout() throws SolverException, InterruptedException {
    requireInterpolation();
    requireIntegers();
    TruthJUnit.assume()
        .withMessage(solverToUse() + " does not support interruption")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.BOOLECTOR);
    testBasicProverTimeoutInt(() -> context.newProverEnvironmentWithInterpolation());
  }

  @Test
  public void testOptimizationProverTimeout() throws SolverException, InterruptedException {
    requireOptimization();
    requireIntegers();
    testBasicProverTimeoutInt(() -> context.newOptimizationProverEnvironment());
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicProverTimeoutInt(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws SolverException, InterruptedException {
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula instance = gen.generate(20);
    expectedEx.expect(InterruptedException.class);
    Thread t =
        new Thread() {
          @Override
          public void run() {
            try {
              sleep(1);
              shutdownManager.requestShutdown("Shutdown Request");
            } catch (InterruptedException pE) {
              throw new UnsupportedOperationException("Unexpected interrupt");
            }
          }
        };
    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      pe.push(instance);
      t.start();
      pe.isUnsat();
    }
  }

  @SuppressWarnings("CheckReturnValue")
  private void testBasicProverTimeoutBv(Supplier<BasicProverEnvironment<?>> proverConstructor)
      throws InterruptedException, SolverException {
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    BooleanFormula instance = gen.generate(20);
    expectedEx.expect(InterruptedException.class);
    Thread t =
        new Thread() {
          @Override
          public void run() {
            try {
              sleep(1);
              shutdownManager.requestShutdown("Shutdown Request");
            } catch (InterruptedException pE) {
              throw new UnsupportedOperationException("Unexpected interrupt");
            }
          }
        };
    try (BasicProverEnvironment<?> pe = proverConstructor.get()) {
      pe.push(instance);
      t.start();
      pe.isUnsat();
    }
  }
}
