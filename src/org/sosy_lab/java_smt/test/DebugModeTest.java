// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableList;
import java.util.List;
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
  private SolverContextFactory debugFactory;

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
            .setOption("solver.useDebugMode", String.valueOf(true))
            .build();
    debugFactory = new SolverContextFactory(debugConfig, logger, shutdownNotifierToUse());
    debugContext = debugFactory.generateContext();

    FormulaManager debugMgr = debugContext.getFormulaManager();
    try {
      debugFmgr = debugMgr.getUFManager();
      debugBmgr = debugMgr.getBooleanFormulaManager();
      debugImgr = debugMgr.getIntegerFormulaManager();
    } catch (UnsupportedOperationException e) {
      // Boolector does not support integer theory. We just leave debugImgr set to null.
    }
  }

  @After
  public void cleanup() {
    if (debugContext != null) {
      debugContext.close();
    }
  }

  /**
   * Helper method for threadLocalTest(). Will rethrow any exception that occurred on the other
   * thread.
   */
  private void checkForExceptions(Future<?> task) {
    try {
      // Accessing the future will rethrow the exception on the main thread
      assert task.get() == null;
    } catch (ExecutionException e) {
      Throwables.throwIfInstanceOf(e.getCause(), IllegalStateException.class);
      Throwables.throwIfUnchecked(e.getCause());
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  /** Try to use the context from a different thread. */
  @SuppressWarnings("resource")
  @Test
  public void nonLocalThreadTest() {
    // Fails for Boolector as debug mode requires visitor support
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);

    ExecutorService exec = Executors.newSingleThreadExecutor();
    Future<?> result =
        exec.submit(
            () -> {
              // Generate a non trivial problem for our tests
              BooleanFormula varA = debugBmgr.makeVariable("a");
              BooleanFormula formula = debugBmgr.and(varA, debugBmgr.not(varA));

              try (BasicProverEnvironment<?> prover = debugContext.newProverEnvironment()) {
                prover.push(formula);
                assertThat(prover).isUnsatisfiable();
              }
              return null;
            });

    // We expect debug mode to throw an exception only on CVC5
    if (solverToUse() == Solvers.CVC5) {
      assertThrows(IllegalStateException.class, () -> checkForExceptions(result));
    } else {
      checkForExceptions(result);
    }
    exec.shutdownNow();
  }

  /**
   * Helper method for noSharedFormulasTest(). Will use the debug context to check the formula for
   * satisfiability.
   *
   * @param pFormula This formula should come from a different context
   */
  private void checkFormulaInDebugContext(BooleanFormula pFormula)
      throws InterruptedException, SolverException {
    try (BasicProverEnvironment<?> prover = debugContext.newProverEnvironment()) {
      prover.push(pFormula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  /** Create a formula then try using it from a different context. */
  @Test
  public void noSharedFormulasTest()
      throws InterruptedException, SolverException, InvalidConfigurationException {
    requireIntegers();

    // Fails for Boolector as debug mode requires visitor support
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);

    try (SolverContext newContext = debugFactory.generateContext()) {
      BooleanFormulaManager newBmgr = newContext.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager newImgr = newContext.getFormulaManager().getIntegerFormulaManager();

      HardIntegerFormulaGenerator hardProblem = new HardIntegerFormulaGenerator(newImgr, newBmgr);
      BooleanFormula formula = hardProblem.generate(DEFAULT_PROBLEM_SIZE);

      // We expect debug mode to throw an exception for all solvers, except CVC4, CVC5 and Yices
      if (!List.of(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2).contains(solverToUse())) {
        assertThrows(IllegalArgumentException.class, () -> checkFormulaInDebugContext(formula));
      } else {
        checkFormulaInDebugContext(formula);
      }
    }
  }

  /**
   * Helper method for noSharedDeclarationsTest(). Uses the function declaration in debug context.
   *
   * @param pDeclaration A function declaration from a different context.
   */
  @SuppressWarnings("ResultOfMethodCallIgnored")
  public void checkDeclarationInDebugContext(FunctionDeclaration<IntegerFormula> pDeclaration) {
    debugFmgr.callUF(pDeclaration, debugImgr.makeNumber(0));
  }

  /** Declare a function, then try calling it from a different context. */
  @Test
  public void noSharedDeclarationsTest() throws InvalidConfigurationException {
    requireIntegers();

    // Fails for Boolector as debug mode requires visitor support
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);

    try (SolverContext newContext = debugFactory.generateContext()) {
      UFManager newFmgr = newContext.getFormulaManager().getUFManager();
      FunctionDeclaration<IntegerFormula> id =
          newFmgr.declareUF(
              "id", FormulaType.IntegerType, ImmutableList.of(FormulaType.IntegerType));

      // We expect debug mode to throw an exception for all solvers, except Princess, CVC4 and Yices
      if (!List.of(Solvers.PRINCESS, Solvers.CVC5, Solvers.YICES2).contains(solverToUse())) {
        assertThrows(IllegalArgumentException.class, () -> checkDeclarationInDebugContext(id));
      } else {
        checkDeclarationInDebugContext(id);
      }
    }
  }

  /** Try to add a formula from a different solver to our solver context. */
  @Test(expected = IllegalArgumentException.class)
  public void noSharingBetweenSolversTest()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    // Compare the solver-under-test with another solver instance.
    // We use Java-based solvers as reference to run on any operating system.
    Solvers otherSolver =
        solverToUse() == Solvers.SMTINTERPOL ? Solvers.PRINCESS : Solvers.SMTINTERPOL;

    try (SolverContext otherContext = debugFactory.generateContext(otherSolver)) {
      BooleanFormulaManager otherBmgr = otherContext.getFormulaManager().getBooleanFormulaManager();
      BooleanFormula formula = otherBmgr.makeFalse();

      try (BasicProverEnvironment<?> prover = debugContext.newProverEnvironment()) {
        // This should fail for all solvers
        prover.push(formula);
        assertThat(prover).isUnsatisfiable();
      }
    }
  }
}
