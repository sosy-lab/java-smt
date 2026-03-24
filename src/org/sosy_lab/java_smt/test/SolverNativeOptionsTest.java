/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class SolverNativeOptionsTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingTimeoutTest() throws InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // (Do not ever use @Test(timeout = ...) on Z3! It SIGSEGVs!
    List<BooleanFormula> parsedCHC = mgr.parseAll(HORN_SMT2);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : parsedCHC) {
        pe.addConstraint(hc);
      }
      // Default Z3 runs endlessly for this HORN task
      buildShutdownThreadWith(shutdownManager, 3000).start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // HORN program of simpleHornSolvingTimeoutTest() succeeds with HORN in Z3
    setAdditionalConfigOptionForSolver("solver.z3.logic", "HORN");

    List<BooleanFormula> parsedCHC = mgr.parseAll(HORN_SMT2);
    // Z3 with HORN can solve this basically instantly!
    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      for (BooleanFormula formula : parsedCHC) {
        prover.addConstraint(formula);
      }
      // Default Z3 runs endlessly for this HORN task, but setting logic HORN makes it finish
      buildShutdownThreadWith(shutdownManager, 5000).start();
      assertThat(prover.isUnsat()).isFalse();
    }
  }

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingWithSpacerTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // HORN program of simpleHornSolvingTimeoutTest() succeeds with HORN in Spacer (Z3)
    // Note: seems like we don't need the option spacer.logic=HORN
    // The options are recommended for this kind of problem, but not needed in general.
    setAdditionalConfigOptionForSolver(
        "solver.z3.logic",
        "HORN",
        "solver.z3.engine",
        "spacer",
        "solver.z3.furtherOptions",
        "spacer.order_children=2,xform.inline_eager=false,xform"
            + ".inline_linear=false,xform.slice=false,spacer.max_level=10");

    List<BooleanFormula> parsedCHC = mgr.parseAll(HORN_SMT2);
    // Spacer can solve this basically instantly!
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : parsedCHC) {
        pe.addConstraint(hc);
      }
      // Default Z3 runs endlessly for this HORN task, but setting logic HORN and using Spacer makes
      // it finish fast (faster than without using Spacer)
      buildShutdownThreadWith(shutdownManager, 5000).start();
      assertThat(pe.isUnsat()).isFalse();
    }
  }

  // TODO: generalize this for all solvers that support "additional" options
  @Test
  public void additionalOptionsTest() throws InvalidConfigurationException {
    assume().that(solver).isEqualTo(Solvers.Z3);
    // We already test bool, symbol, string and unsigned int with the engine test
    // Start with 1 additional option
    setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "restart_factor=2");
    // Now 2
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.epsilon=2," + "restart_factor=2");
    // With spaces
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.epsilon = 2," + " restart_factor = 2");
    // Capitalized
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.Epsilon=2," + "Restart_facTor=2");
  }

  // Test that options are not allowed to be existing twice
  @Test
  public void additionalOptionsDoubleTest() {
    assume().that(solver).isEqualTo(Solvers.Z3);
    assertThrows(
        IllegalArgumentException.class,
        () ->
            setAdditionalConfigOptionForSolver(
                "solver.z3.furtherOptions", "restart_factor=2,arith.epsilon=2,restart_factor=3"));
  }

  // TODO: generalize this for all solvers that support "additional" options
  @Test
  public void additionalOptionsFailTest() {
    assume().that(solver).isEqualTo(Solvers.Z3);
    // Z3 disallows certain option combinations
    final Set<String> disallowedConfigurationOptionsZ3 =
        ImmutableSet.of(
            "engine=spacer",
            "optsmt_engine=true",
            "priority=box",
            "logic=ALL",
            "unsat_core=true",
            "model=true",
            "random_seed=42",
            "smt.random_seed=42",
            "proof=true");
    for (final String optionWithValue : disallowedConfigurationOptionsZ3) {
      assertThrows(
          IllegalArgumentException.class,
          () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", optionWithValue));
    }
  }

  // TODO: generalize LOGIC tests and move into their own test class once more solvers support this!
  // Z3 solves the query from z3AllLogicOnBvProblemTest() much faster if we set the logic.
  @Test
  public void z3QFBVLogicOnBvProblemTest()
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // QF_BV solves this problem in ~2s, much faster than ALL (~17s)
    // You can test this by commenting out the following line:
    setAdditionalConfigOptionForSolver("solver.z3.logic", "QF_BV");

    List<BooleanFormula> bvFormulasWithLogic =
        context
            .getFormulaManager()
            .parseAll(
                Files.readString(Path.of("src/org/sosy_lab/java_smt/test/manyRegReads.smt2")));

    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : bvFormulasWithLogic) {
        // We need incremental solving to see the difference
        // (which is only active after pushing something)
        pe.push(hc);
      }
      // Finishes in ~2s with logic QF_BV, but takes 17s+ with default (ALL).
      buildShutdownThreadWith(shutdownManager, 4000).start();
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // Z3 solves the given query in roughly ~9s normally, but by setting an option, it is much faster
  @Test
  public void z3FasterWithOptionsTest()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // 'arith.solver=6' conforms to LRA (default) and solving takes about ~9s
    // 'arith.solver=2' uses a Simplex-based solver and solving takes roughly ~4.5s for this task
    // 'arith.solver=5' uses infinitary LRA and solving takes roughly ~4.5s
    // 'arith.solver=3', uses Floyd-Warshall, which solves in ~3s (3x faster than LRA)
    // The times might change over time due to Z3 updates and are based on when this test was
    // implemented! You can set the different options in the config line below to test this out!
    // Original source: https://github.com/Z3Prover/z3/issues/8940#issuecomment-4106152740
    setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "arith.solver=2");

    List<BooleanFormula> fs =
        context
            .getFormulaManager()
            .parseAll(Files.readString(Path.of("src/org/sosy_lab/java_smt/test/client.smt2")));
    assertThat(fs.size()).isEqualTo(8);

    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      // The program used incremental solving that we can't parse currently.
      // The stack was pushed once with the second to last assertion
      // Before asserting the last assert, the stack was popd.
      for (int i = 0; i < fs.size() - 2; i++) {
        pe.addConstraint(fs.get(i));
      }
      pe.push(fs.get(fs.size() - 2));
      pe.pop();
      pe.addConstraint(fs.get(fs.size() - 1));

      // The query should be solved in ~3s with the correct (non-default) option set, but takes
      // ~9s for default options
      buildShutdownThreadWith(shutdownManager, 5000).start();
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  // Small HORN problem in SMT2
  private static final String HORN_SMT2 =
      "(declare-fun Itp (Int Int) Bool)\n"
          + "(assert (forall ((a Int) (x Int) (b Int)) (=> (and (< a x) (< x b)) (Itp a b))))\n"
          + "(assert (forall ((a Int) (b Int)) (=> (Itp a b) (not (< b a)))))";

  // TODO: either move to SolverBasedTest0 or even better include into the assertion framework
  /**
   * Creates and returns a new {@link Thread}, that has not been started, with a sleep of
   * millisTillShutdown in milliseconds before a shutdown is requested by the given {@link
   * ShutdownManager}.
   */
  private static Thread buildShutdownThreadWith(
      ShutdownManager pShutdownManager, long millisTillShutdown) {
    // (Do not ever use @Test(timeout = ...) on Z3! It SIGSEGVs!
    return new Thread(
        () -> {
          try {
            Thread.sleep(millisTillShutdown);
            pShutdownManager.requestShutdown("Shutdown Request");
          } catch (InterruptedException exception) {
            throw new UnsupportedOperationException("Unexpected interrupt", exception);
          }
        });
  }
}
