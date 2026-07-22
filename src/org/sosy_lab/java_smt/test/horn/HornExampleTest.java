/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.horn;

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

public class HornExampleTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void hornJavaSMT() throws Exception {
    requireHorn();
    var intf = context.getFormulaManager().getIntegerFormulaManager();
    var horn = context.getFormulaManager().getBooleanFormulaManager();

    var varA = horn.makeVariable("a");
    var varB = horn.makeVariable("b");
    var varC = horn.makeVariable("c");

    var varE = intf.makeVariable("e");
    var n1 = intf.makeNumber(1);


    var clause1 = horn.makeHornClause(varA, jList(varB, varC), intf.greaterOrEquals(varE, n1));
    var clause2 = horn.makeHornClause(jList(varB)); // TODO: Simplify to true???
    var clause3 = horn.makeHornClause(varA, jList(varC));
    {

      var prover = context.newProverEnvironment();

      prover.addConstraint(clause1);
      prover.addConstraint(clause2);
      prover.addConstraint(clause3);

      assertFalse(prover.isUnsat());
    }
    {
      var prover = context.newHornProverEnvironment();

      prover.addConstraint(clause1);
      prover.addConstraint(clause2);
      prover.addConstraint(clause3);

      assertFalse(prover.isUnsat());
    }
  }

  @Test
  public void hornJavaSMTPredicate() throws Exception {
    requireHorn();
    // Pretty much taken from https://github.com/uuverifiers/eldarica/blob/master/src/test/scala/lazabs/horn/HornAPI.scala#L55
    var integer = context.getFormulaManager().getIntegerFormulaManager();
    var horn = context.getFormulaManager().getBooleanFormulaManager();
    var uf = context.getFormulaManager().getUFManager();


    var p0 = uf.declareUF("p0", FormulaType.BooleanType, FormulaType.IntegerType);
    var p1 = uf.declareUF("p1", FormulaType.BooleanType, FormulaType.IntegerType);
    var p2 = uf.declareUF("p2", FormulaType.BooleanType, FormulaType.IntegerType);

    var n0 = integer.makeNumber(0);
    var n1 = integer.makeNumber(1);
    var n2 = integer.makeNumber(2);

    var x = integer.makeVariable("x");

    var p0X = uf.callUF(p0, jList(x));
    var p0X_1 = uf.callUF(p0, jList(integer.subtract(x, n1)));
    var p1X = uf.callUF(p1, jList(x));
    var p2X = uf.callUF(p2, jList(x));


    var clause1 = horn.makeHornClause(p0X, jList(), integer.greaterThan(x, n2));
    var clause2 = horn.makeHornClause(p1X, jList(p0X), integer.greaterThan(x, n0));
    var clause3 = horn.makeHornClause(p0X_1, jList(p1X));
    var clause4 = horn.makeHornClause(p2X, jList(p0X), integer.lessOrEquals(x, n0));
    var clause5 = horn.makeHornClause(jList(p2X), integer.greaterOrEquals(x, n0));
    {
      var prover = context.newProverEnvironment();

      prover.addConstraint(clause1);
      prover.addConstraint(clause2);
      prover.addConstraint(clause3);
      prover.addConstraint(clause4);
      prover.addConstraint(clause5);

      assertFalse(prover.isUnsat());
    }
    {
      var prover = context.newHornProverEnvironment();

      prover.addConstraint(clause1);
      prover.addConstraint(clause2);
      prover.addConstraint(clause3);
      prover.addConstraint(clause4);
      prover.addConstraint(clause5);

      assertFalse(prover.isUnsat());
    }
  }

  @SuppressWarnings("DefaultCharset")
  private HornProverEnvironment solveSmtLib2(
      final String file,
      SolverContext.ProverOptions... options) throws Exception {
    requireHorn();
    var path = "/org/sosy_lab/java_smt/test/horn/" + file + ".smt2";
    var stream = HornExampleTest.class.getResourceAsStream(path);
    var input = new String(stream.readAllBytes());
    stream.close();

    var formula = context.getFormulaManager();
    var constraints = formula.parseAll(input);

    var prover = context.newHornProverEnvironment(options);

    for (var constraint : constraints) {
      prover.addConstraint(constraint);
    }

    return prover;
  }


  @Test
  public void smt_02_c_000() throws Exception {
    var prover = solveSmtLib2("02.c_000");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_01_c_bv_000() throws Exception {
    var prover = solveSmtLib2("01.c-bv_000");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_ch_triangle_location_nr_2_bv_000() throws Exception {
    var prover = solveSmtLib2("ch-triangle-location-nr.2-bv_000");

    assertTrue(prover.isUnsat());
  }

  @Test
  public void smt_prusti_3_pass_paper_Examples_points_compress_000() throws Exception {
    var prover = solveSmtLib2("prusti-3-pass-paper_examples-points-compress_000");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_38_c_000() throws Exception {
    assume().that(solver).isNotEqualTo(Solvers.ELDARICA); // ex
    var prover = solveSmtLib2("38.c_000");

    assertFalse(prover.isUnsat());
  }

  // test for ex quantifier inside formula
  @Test
  public void smt_s_split_09_000() throws Exception {
    assume().that(solver).isNotEqualTo(Solvers.ELDARICA);
    var prover = solveSmtLib2("s_split_09_000");

    assertTrue(prover.isUnsat());
  }


  // test for rewriting equation ITE terms and epsilon terms
  @Test
  public void smt_s_split_18_000() throws Exception {
    assume().that(solver).isNotEqualTo(Solvers.ELDARICA); // ex
    var prover = solveSmtLib2("s_split_18_000");

    assertFalse(prover.isUnsat());
  }

  // test for rewriting deep nested ITE terms
  @Test
  public void smt_rewrite_ite() throws Exception {
    var prover = solveSmtLib2("rewrite_ite");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_two_counters_e3_325_000() throws Exception {
    var prover = solveSmtLib2("two_counters_e3_325_000");

    assertTrue(prover.isUnsat());
  }

  @Test
  public void smt_O0_fibo_10_false_unreach_call_000() throws Exception {
    var prover = solveSmtLib2("O0_fibo_10_false-unreach-call_000");

    assertTrue(prover.isUnsat());
  }


  @Test
  public void smt_O0_count_up_down_false_unreach_call_true_termination_000() throws Exception {
    var prover = solveSmtLib2("O0_count_up_down_false-unreach-call_true-termination_000");

    assertTrue(prover.isUnsat());
  }

  @Test
  public void smt_shift_right_negative_lvalue_int16_sol_2_000() throws Exception {
    var prover = solveSmtLib2("shift_right_negative_lvalue_int16.sol_2_000");

    assertTrue(prover.isUnsat());
  }

  @Test
  public void smt_s_split_37_000() throws Exception {
    var prover = solveSmtLib2("s_split_37_000");

    assertTrue(prover.isUnsat());
  }

  @Test
  public void smt_s_split_23_000() throws Exception { // endless looking for interpolants
    var prover = solveSmtLib2("s_split_23_000");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_small_unsat() throws Exception {
    /*
    mc(A,B) :- ((A + -100) >= 1),(B = (A + -10)).
    mc(A,B) :- (A =< 100),mc(C,B),(D = (A + 11)),mc(D,C).
    false :- \+((A = 91)),(B =< 101),mc(B,A).
     */

    var prover = solveSmtLib2("small_unsat");

    assertTrue(prover.isUnsat());
  }


  @Test
  public void smt_small_sat() throws Exception {
    /*
    mc(A,B) :- ((A + -100) >= 1),(B = (A + -10)).
    mc(A,B) :- (A =< 100),mc(C,B),(D = (A + 11)),mc(D,C).
    false :- \+((A = 91)),(B =< 101),mc(B,A).
     */

    var prover = solveSmtLib2("small_sat");

    assertFalse(prover.isUnsat());
  }

  @Test
  public void smt_small_unsat_model() throws Exception {
    var prover = solveSmtLib2("small_unsat", ProverOptions.GENERATE_MODELS);

    prover.isUnsat();
    assertThrows(Exception.class, () -> prover.getModel());
  }

  @Test
  public void smt_small_sat_model() throws Exception {
    var prover = solveSmtLib2("small_sat", ProverOptions.GENERATE_MODELS);

    prover.isUnsat();
    var model = prover.getModel().asList();

    assertEquals(1, model.size());

    var fun = model.iterator().next();

    assertEquals("fun", fun.getName());
    assertTrue(fun.getAssignmentAsFormula().toString().contains("-91 + _1"));
    var value = (Object[]) fun.getValue();
    assertEquals(2, value.length);
    assertNull(value[0]); // does not matter
    assertEquals(BigInteger.valueOf(91), value[1]);
  }

  @SuppressWarnings("varargs")
  @SafeVarargs
  private <A> java.util.List<A> jList(A... vars) {
    return java.util.Arrays.asList(vars);
  }
}
