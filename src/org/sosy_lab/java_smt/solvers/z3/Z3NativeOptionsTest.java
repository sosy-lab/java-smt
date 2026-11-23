/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

public class Z3NativeOptionsTest extends SolverBasedTest0 {

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  // Small HORN problem in SMT2 (assertions should be asserted individually and not as a
  // conjunction! Otherwise the solvers don't recognize this as HORN!)
  private static final String HORN_SMT2 =
      """
      (declare-fun Itp (Int Int) Bool)
      (assert (forall ((a Int) (x Int) (b Int)) (=> (and (< a x) (< x b)) (Itp a b))))
      (assert (forall ((a Int) (b Int)) (=> (Itp a b) (not (< b a)))))
      """;

  private static final String SIMPLIFIERS = "simplify, propagate-values, simplify, solve-eqs";

  // Pre-processing tactics followed by the tactic smt, which decides satisfiability
  private static final String TACTICS = "simplify, solve-eqs, smt";

  // Statistics key of the simplifier solve-eqs in Z3 (see src/ast/simplifiers/solve_eqs.cpp)
  private static final String SOLVE_EQS_ELIM_VARS_KEY = "solve-eqs-elim-vars";

  @Override
  protected Solvers solverToUse() {
    return Solvers.Z3;
  }

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingTimeoutTest() throws InterruptedException {
    // (Do not ever use @Test(timeout = ...) on Z3! It SIGSEGVs!
    List<BooleanFormula> parsedCHC = mgr.parseAll(HORN_SMT2);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : parsedCHC) {
        pe.addConstraint(hc);
      }
      // Default Z3 runs endlessly for this HORN task (not solved within 60s), while Z3 with logic
      // HORN solves it within milliseconds (see simpleHornSolvingTest), so a short timeout suffices
      buildShutdownThreadWith(shutdownManager, 500).start();
      assertThrows(InterruptedException.class, pe::isUnsat);
    }
  }

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
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
    // We already test bool, symbol, string and unsigned int with the engine test
    // Start with 1 additional option
    setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "restart_factor=2");
    // Now 2
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.epsilon=2,restart_factor=2");
    // With spaces
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.epsilon = 2, restart_factor = 2");
    // Capitalized
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.Epsilon=2,Restart_facTor=2");
  }

  // Test that options are not allowed to be existing twice
  @Test
  public void additionalOptionsDoubleTest() {
    assertThrows(
        IllegalArgumentException.class,
        () ->
            setAdditionalConfigOptionForSolver(
                "solver.z3.furtherOptions", "restart_factor=2,arith.epsilon=2,restart_factor=3"));
  }

  // TODO: generalize this for all solvers that support "additional" options
  @Test
  public void additionalOptionsFailTest() {
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
  // TODO: ignored due to AppVeyor in our CI being so slow that this fails often
  @Ignore
  @Test
  public void z3FasterWithAirthSolverOptionsTest()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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
    assertThat(fs).hasSize(8);

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
      // ~9s for default options. We use 7.5s as timeout as the CI is a little slower.
      buildShutdownThreadWith(shutdownManager, 7500).start();
      assertThat(pe.isUnsat()).isTrue();
    }
  }

  @Test
  public void unknownSimplifierTest() {
    InvalidConfigurationException exception =
        assertThrows(
            InvalidConfigurationException.class,
            () ->
                setAdditionalConfigOptionForSolver(
                    "solver.z3.simplifiers", "solve-eqs, unknown-simplifier"));
    assertThat(exception).hasMessageThat().contains("unknown-simplifier");
  }

  @Test
  public void simplifierApplicationTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    // Without push(), Z3 solves non-incrementally and applies solve-eqs as a tactic anyway.
    // Simplifiers are designed for incremental solving, so we push() before adding constraints.

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push();
      prover.addConstraint(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.addConstraint(imgr.equal(y, imgr.makeNumber(3)));
      assertThat(prover.isUnsat()).isFalse();
      assertThat(prover.getStatistics()).doesNotContainKey(SOLVE_EQS_ELIM_VARS_KEY);
    }

    setAdditionalConfigOptionForSolver("solver.z3.simplifiers", SIMPLIFIERS);

    x = imgr.makeVariable("x");
    y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push();
      prover.addConstraint(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.addConstraint(imgr.equal(y, imgr.makeNumber(3)));
      prover.addConstraint(imgr.greaterThan(x, z));
      assertThat(prover.isUnsat()).isFalse();
      assertThat(Integer.parseInt(prover.getStatistics().get(SOLVE_EQS_ELIM_VARS_KEY)))
          .isGreaterThan(0);

      // The model needs to contain correct values for eliminated variables
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(4));
        assertThat(model.evaluate(y)).isEqualTo(BigInteger.valueOf(3));
        assertThat(model.evaluate(z)).isLessThan(BigInteger.valueOf(4));
      }
    }
  }

  @Test
  public void incrementalSolvingWithSimplifiersTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {

    setAdditionalConfigOptionForSolver("solver.z3.simplifiers", SIMPLIFIERS);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.push(imgr.equal(y, imgr.makeNumber(3)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(4));
      }

      prover.push(imgr.greaterThan(x, imgr.makeNumber(10)));
      assertThat(prover.isUnsat()).isTrue();
      prover.pop();
      assertThat(prover.isUnsat()).isFalse();

      // Popping the definition of y must undo its elimination
      prover.pop();
      prover.push(imgr.equal(y, imgr.makeNumber(20)));
      prover.push(imgr.greaterThan(x, imgr.makeNumber(10)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(21));
        assertThat(model.evaluate(y)).isEqualTo(BigInteger.valueOf(20));
      }
    }
  }

  @Test
  public void simplifiersWithLogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {

    setAdditionalConfigOptionForSolver(
        "solver.z3.simplifiers", SIMPLIFIERS, "solver.z3.logic", "QF_LIA");

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.addConstraint(imgr.equal(y, imgr.makeNumber(3)));
      assertThat(prover.isUnsat()).isFalse();
      prover.addConstraint(imgr.greaterThan(x, imgr.makeNumber(4)));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

  /** Creates and closes many provers with simplifiers to exercise the reference counting. */
  @SuppressWarnings("resource")
  @Test
  public void manyProversWithSimplifiersTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.z3.simplifiers", SIMPLIFIERS);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    for (int round = 0; round < 10; round++) {
      List<ProverEnvironment> provers = new ArrayList<>();
      for (int i = 0; i < 10; i++) {
        ProverEnvironment prover = context.newProverEnvironment();
        prover.addConstraint(imgr.equal(x, imgr.add(y, imgr.makeNumber(i))));
        prover.addConstraint(imgr.equal(y, imgr.makeNumber(round)));
        provers.add(prover);
      }
      for (int i = 0; i < provers.size(); i++) {
        ProverEnvironment prover = provers.get(i);
        prover.push(imgr.equal(x, imgr.makeNumber(round + i)));
        assertThat(prover.isUnsat()).isFalse();
        prover.pop();
        prover.push(imgr.equal(x, imgr.makeNumber(round + i + 1)));
        assertThat(prover.isUnsat()).isTrue();
      }
      // close in an order different from the creation order
      for (ProverEnvironment prover : Lists.reverse(provers)) {
        prover.close();
      }
    }
  }

  @Test
  public void unsatCoresWithSimplifiersTest() throws InvalidConfigurationException {
    setAdditionalConfigOptionForSolver("solver.z3.simplifiers", SIMPLIFIERS);
    assertThrows(
        UnsupportedOperationException.class,
        () -> context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE));
    assertThrows(
        UnsupportedOperationException.class,
        () -> context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS));
  }

  @Test
  public void assumptionsWithSimplifiersTest()
      throws InvalidConfigurationException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.z3.simplifiers", SIMPLIFIERS);
    IntegerFormula x = imgr.makeVariable("x");
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(imgr.equal(x, imgr.makeNumber(1)));
      assertThrows(
          UnsupportedOperationException.class,
          () -> prover.isUnsatWithAssumptions(ImmutableList.of(imgr.equal(x, imgr.makeNumber(2)))));
    }
  }

  @Test
  public void unknownTacticTest() {
    InvalidConfigurationException exception =
        assertThrows(
            InvalidConfigurationException.class,
            () -> setAdditionalConfigOptionForSolver("solver.z3.tactics", "smt, unknown-tactic"));
    assertThat(exception).hasMessageThat().contains("unknown-tactic");
  }

  @Test
  public void tacticsWithLogicOrEngineTest() {
    assertThrows(
        InvalidConfigurationException.class,
        () ->
            setAdditionalConfigOptionForSolver(
                "solver.z3.tactics", TACTICS, "solver.z3.logic", "QF_LIA"));
    assertThrows(
        InvalidConfigurationException.class,
        () ->
            setAdditionalConfigOptionForSolver(
                "solver.z3.tactics", TACTICS, "solver.z3.engine", "bmc"));
  }

  @Test
  public void tacticsAreAppliedTest() throws InvalidConfigurationException, InterruptedException {
    // The tactic simplify can not decide the satisfiability of x > y, but the default solver can
    setAdditionalConfigOptionForSolver("solver.z3.tactics", "simplify");
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(imgr.greaterThan(x, y));
      assertThrows(SolverException.class, prover::isUnsat);
    }
  }

  @Test
  public void incrementalSolvingWithTacticsTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.z3.tactics", TACTICS);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.push(imgr.equal(y, imgr.makeNumber(3)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(4));
      }

      prover.push(imgr.greaterThan(x, imgr.makeNumber(10)));
      assertThat(prover.isUnsat()).isTrue();
      prover.pop();
      prover.pop();
      prover.push(imgr.equal(y, imgr.makeNumber(20)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(21));
      }
    }
  }

  @Test
  public void unsatCoresWithTacticsTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.z3.tactics", TACTICS);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");
    BooleanFormula xIsYPlusOne = imgr.equal(x, imgr.add(y, imgr.makeNumber(1)));
    BooleanFormula yIsThreeAndXGreaterZ =
        bmgr.and(imgr.equal(y, imgr.makeNumber(3)), imgr.greaterThan(x, z));
    BooleanFormula zGreaterTen = imgr.greaterThan(z, imgr.makeNumber(10));
    BooleanFormula zGreaterMinusFive = imgr.greaterThan(z, imgr.makeNumber(-5));

    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      prover.addConstraint(xIsYPlusOne);
      prover.addConstraint(yIsThreeAndXGreaterZ);
      prover.push(zGreaterTen);
      prover.addConstraint(zGreaterMinusFive);
      assertThat(prover.isUnsat()).isTrue();
      assertThat(prover.getUnsatCore())
          .containsExactly(xIsYPlusOne, yIsThreeAndXGreaterZ, zGreaterTen);
    }

    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      prover.addConstraint(bmgr.not(a));
      assertThat(prover.isUnsatWithAssumptions(ImmutableList.of(b))).isFalse();
      assertThat(prover.unsatCoreOverAssumptions(ImmutableList.of(a, b)).orElseThrow())
          .containsExactly(a);
    }
  }

  @Test
  public void userPropagatorWithTacticsTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    // User propagators are not supported with tactics, also not with tactics ending with 'smt'
    for (String tactics : ImmutableList.of("default", TACTICS)) {
      setAdditionalConfigOptionForSolver("solver.z3.tactics", tactics);
      try (ProverEnvironment prover = context.newProverEnvironment()) {
        assertThat(prover.registerUserPropagator(new AbstractUserPropagator() {})).isFalse();
        // The prover is still usable
        prover.push(bmgr.makeVariable("p"));
        assertThat(prover.isUnsat()).isFalse();
      }
    }
  }

  @Test
  public void tacticsWithSimplifiersTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver(
        "solver.z3.tactics", TACTICS, "solver.z3.simplifiers", SIMPLIFIERS);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(x, imgr.add(y, imgr.makeNumber(1))));
      prover.push(imgr.equal(y, imgr.makeNumber(3)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(BigInteger.valueOf(4));
      }
      prover.push(imgr.greaterThan(x, imgr.makeNumber(10)));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

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
