// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;

public class DebugModeTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  private SolverContext debugContext;
  private UFManager debugFmgr;
  private BooleanFormulaManager debugBmgr;
  private IntegerFormulaManager debugImgr;

  private static final int DEFAULT_PROBLEM_SIZE = 8;

  @Before
  public void init() throws InvalidConfigurationException {
    Configuration debugConfig =
        Configuration.builder()
            .setOption("solver.solver", solverToUse().toString())
            .setOption("solver.debugMode", String.valueOf(true))
            .build();
    SolverContextFactory debuggingFactory =
        new SolverContextFactory(debugConfig, logger, shutdownNotifierToUse());

    debugContext = debuggingFactory.generateContext();
    try {
      FormulaManager debugMgr = debugContext.getFormulaManager();

      debugFmgr = debugMgr.getUFManager();
      debugBmgr = debugMgr.getBooleanFormulaManager();
      debugImgr = debugMgr.getIntegerFormulaManager();
    } catch (UnsupportedOperationException e) {
      // Boolector does not support integers and throws an exception. In this case we'll just
      // leave the formula manager set to null
    }
  }

  @After
  public void cleanup() {
    if (debugContext != null) {
      debugContext.close();
    }
  }

  @SuppressWarnings("resource")
  @Test(expected = IllegalStateException.class)
  public void wrongThreadTest() throws InterruptedException {
    requireIntegers();
    HardIntegerFormulaGenerator hardProblem = new HardIntegerFormulaGenerator(debugImgr, debugBmgr);

    // Try to use the context in a different thread
    ExecutorService exec = Executors.newSingleThreadExecutor();
    Future<?> result =
        exec.submit(
            () -> {
              BooleanFormula formula = hardProblem.generate(DEFAULT_PROBLEM_SIZE);
              try (BasicProverEnvironment<?> prover = debugContext.newProverEnvironment()) {
                prover.push(formula);
                assertThat(prover).isUnsatisfiable();
              }
              return null;
            });

    try {
      assert result.get() == null;
    } catch (ExecutionException e) {
      Throwables.throwIfInstanceOf(e.getCause(), IllegalStateException.class);
      Throwables.throwIfUnchecked(e.getCause());
    }
    exec.shutdownNow();
  }

  @Test(expected = IllegalArgumentException.class)
  public void wrongContextTest() throws InterruptedException, SolverException {
    requireIntegers();
    HardIntegerFormulaGenerator hardProblem = new HardIntegerFormulaGenerator(imgr, bmgr);

    // FIXME: This test tries to use a formula that was created in a different context. We expect
    //  this test to fail for most solvers, but there should be a unique error message.
    //  Right now we get:
    //  OpenSMT claims the formula is satisfiable:
    //    expected to be : unsatisfiable
    //    but was        : org.sosy_lab.java_smt.solvers.opensmt.OpenSmtTheoremProver@10d59286
    //    which is       : satisfiable
    //    which has model:
    //  MathSAT5 thows an IllegalStateExpression:
    //    msat_solve returned "unknown": polarity information is meaningful only for terms of
    //    type Bool
    //  SMTInterpol thows an de.uni_freiburg.informatik.ultimate.logic.SMTLIBException:
    //    Asserted terms created with incompatible theory
    //  Z3 throws an com.microsoft.z3.Z3Exception:
    //    invalid argument
    //  Princess throws an java.util.NoSuchElementException:
    //    key not found: i@15
    //  Boolector crashes with a segfault:
    //    boolector_assert: argument 'exp' belongs to different Boolector instance
    //
    // To fix this issue, we would need to track which formula was created in which context,
    // which might result in quite some management and memory overhead.
    // We might want to see this as very low priority, as there is no real benefit for the user,
    // except having a nice error message.

    // Boolector does not support integer, so we have to use two different versions for this test.
    BooleanFormula formula =
        solverToUse() == Solvers.BOOLECTOR
            ? bmgr.makeFalse()
            : hardProblem.generate(DEFAULT_PROBLEM_SIZE);

    try (BasicProverEnvironment<?> prover = debugContext.newProverEnvironment()) {
      // Try to add a formula from a different context to our debug solver context.
      prover.push(formula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  @SuppressWarnings("unused")
  @Test(expected = IllegalArgumentException.class)
  public void wrongContextUFTest() {
    requireIntegers();
    // Declare the function on the normal context...
    FunctionDeclaration<IntegerFormula> id =
        fmgr.declareUF("id", FormulaType.IntegerType, ImmutableList.of(FormulaType.IntegerType));
    // then try calling it from the debugging context
    IntegerFormula f = debugFmgr.callUF(id, debugImgr.makeNumber(0));
  }
}
