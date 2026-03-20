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
import java.util.List;
import java.util.Set;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.z3.Z3SolverContext;

public class SolverNativeOptionsTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // TODO: HORN test(s) will be moved once we have a dedicated HORN prover and tests
  @Test
  public void simpleHornSolvingTimeoutTest() throws InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // Normal Z3 runs endlessly for this HORN task, so we shut it down after a few seconds
    // (Do not ever use @Test(timeout = ...) on Z3! It SIGSEGVs!
    Thread killerThread =
        new Thread(
            () -> {
              try {
                Thread.sleep(3000); // 3s
                shutdownManager.requestShutdown("Shutdown Request");
              } catch (InterruptedException exception) {
                throw new UnsupportedOperationException("Unexpected interrupt", exception);
              }
            });

    List<BooleanFormula> parsedCHC = mgr.parseAll(HORN_SMT2);
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : parsedCHC) {
        pe.addConstraint(hc);
      }
      killerThread.start();
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
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      for (BooleanFormula hc : parsedCHC) {
        pe.addConstraint(hc);
      }
      assertThat(pe.isUnsat()).isFalse();
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
    Set<String> disallowedConfigurationOptionsZ3 =
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
  @Test
  public void z3QFLIALogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    setAdditionalConfigOptionForSolver("solver.z3.logic", "QF_LIA");
    IntegerFormula zeroInt = imgr.makeNumber(0);
    assertThatFormula(imgr.equal(imgr.add(zeroInt, zeroInt), zeroInt)).isTautological();

    // TODO: is Z3 just ignoring the set logics and solves all if we diverge from it?
    BitvectorFormula zeroBv = bvmgr.makeBitvector(8, 0);
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(zeroBv, zeroBv), zeroBv)).isTautological();
  }

  // Small HORN problem in SMT2
  private static final String HORN_SMT2 =
      "(declare-fun Itp (Int Int) Bool)\n"
          + "(assert (forall ((a Int) (x Int) (b Int)) (=> (and (< a x) (< x b)) (Itp a b))))\n"
          + "(assert (forall ((a Int) (b Int)) (=> (Itp a b) (not (< b a)))))";
}
