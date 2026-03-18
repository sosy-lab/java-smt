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

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import java.util.List;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class SolverNativeOptionsTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void z3EngineTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    // Normal Z3 returns UNKNOWN for this CHC task
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      List<BooleanFormula> parsedCHC = mgr.parseAll(CHC2);
      for (BooleanFormula parsedFormula : parsedCHC) {
        pe.addConstraint(parsedFormula);
      }
      assertThrows(SolverException.class, pe::isUnsat);
    }

    // Switch to CHC solving (and build a new context, as the old one is stopped)
    setAdditionalConfigOptionForSolver("solver.z3.engine", "spacer");
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions",
        "spacer.order_children=2,xform.inline_eager=false,xform.inline_linear=false,xform.slice=false,spacer.max_level=10");

    List<BooleanFormula> parsedCHC = mgr.parseAll(CHC2);
    assertThatFormula(bmgr.and(parsedCHC)).isSatisfiable();
  }

  @Test
  public void additionalOptionsTest() throws InvalidConfigurationException {
    assume().that(solver).isEqualTo(Solvers.Z3);
    // We already test bool, symbol, string and unsigned int with the engine test
    // Start with 1 additional option
    setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "restart_factor=2");
    // Now 2
    setAdditionalConfigOptionForSolver(
        "solver.z3.furtherOptions", "arith.epsilon=2," + "restart_factor=2");

    // Multiple are also tested in the engine test
  }

  @Test
  public void additionalOptionsFailTest() {
    assume().that(solver).isEqualTo(Solvers.Z3);
    // Z3 disallows certain option combinations
    assertThrows(
        IllegalArgumentException.class,
        () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "engine=spacer"));
    assertThrows(
        IllegalArgumentException.class,
        () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "optsmt_engine=true"));
    assertThrows(
        IllegalArgumentException.class,
        () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "priority=box"));
    assertThrows(
        IllegalArgumentException.class,
        () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "logic=ALL"));
    assertThrows(
        IllegalArgumentException.class,
        () -> setAdditionalConfigOptionForSolver("solver.z3.furtherOptions", "spacer.logic=ALL"));
  }

  @Test
  public void z3AllLogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.z3.logic", "all");

    BitvectorFormula zero = bvmgr.makeBitvector(8, 0);
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(zero, zero), zero)).isTautological();
  }

  @Test
  public void z3QFLIALogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    assume().that(solver).isEqualTo(Solvers.Z3);

    setAdditionalConfigOptionForSolver("solver.z3.logic", "QF_LIA");
    IntegerFormula zeroInt = imgr.makeNumber(0);
    assertThatFormula(imgr.equal(imgr.add(zeroInt, zeroInt), zeroInt)).isTautological();

    // TODO: is Z3 just ignoring the set logics?
    BitvectorFormula zeroBv = bvmgr.makeBitvector(8, 0);
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(zeroBv, zeroBv), zeroBv)).isTautological();
  }

  // From
  // https://github.com/chc-comp/chc-comp25-benchmarks/blob/main/extra-small-lia/bouncy_two_counters_merged_000.smt2
  @SuppressWarnings("unused")
  private static final String CHC_SMT2 =
      "(set-logic HORN)\n"
          + "(declare-fun |itp1| ( Int Int Int ) Bool)\n"
          + "(assert\n"
          + "  (forall ( (A Int) (B Int) (C Int) ) \n"
          + "    (=>\n"
          + "      (and\n"
          + "        (and (= B 0) (= A 0) (= C 0))\n"
          + "      )\n"
          + "      (itp1 A B C)\n"
          + "    )\n"
          + "  )\n"
          + ")\n"
          + "(assert\n"
          + "  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) \n"
          + "    (=>\n"
          + "      (and\n"
          + "        (itp1 B A C)\n"
          + "        (or (and (= D B) (= E (+ 1 A)) (= F (+ (- 1) C)))\n"
          + "    (and (= D (+ 1 B)) (= E A) (= F (+ 1 C))))\n"
          + "      )\n"
          + "      (itp1 D E F)\n"
          + "    )\n"
          + "  )\n"
          + ")\n";

  // https://github.com/chc-comp/chc-comp25-benchmarks/blob/main/extra-small-lia/yz_plus_minus_1_000.smt2
  private static final String CHC2 =
      "(declare-fun |inv| ( Int Int Int ) Bool)\n"
          + "\n"
          + "(assert\n"
          + "  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) ) \n"
          + "    (=>\n"
          + "      (and\n"
          + "        (and true (= 0 v_0) (= 0 v_1) (= 0 v_2))\n"
          + "      )\n"
          + "      (inv v_0 v_1 v_2)\n"
          + "    )\n"
          + "  )\n"
          + ")\n"
          + "(assert\n"
          + "  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) \n"
          + "    (=>\n"
          + "      (and\n"
          + "        (inv A C B)\n"
          + "        (and (= E (+ 1 B)) (= D (+ A C)) (not (<= 100 A)) (= F (+ (- 1) C)))\n"
          + "      )\n"
          + "      (inv D E F)\n"
          + "    )\n"
          + "  )\n"
          + ")\n"
          + "(assert\n"
          + "  (forall ( (A Int) (B Int) (C Int) ) \n"
          + "    (=>\n"
          + "      (and\n"
          + "        (inv C A B)\n"
          + "        (not (>= C 0))\n"
          + "      )\n"
          + "      false\n"
          + "    )\n"
          + "  )\n"
          + ")";
}
