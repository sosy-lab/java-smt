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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.HornProverEnvironment;

public class HornExampleTest {
  // TODO: Test with all solvers, not just eldarica (ParameterizedSolverBasedTest0)

  // static {
  //   GlobalParameters.get().setLogLevel(3);
  //   GlobalParameters.get().log_$eq(true);
  // }

  @Test
  public void hornJavaSMT() throws Exception {
    final var context = SolverContextFactory.createSolverContext(Solvers.ELDARICA);

    var intf = context.getFormulaManager().getIntegerFormulaManager();
    var horn = context.getFormulaManager().getBooleanFormulaManager();

    var varA = horn.makeVariable("a");
    var varB = horn.makeVariable("b");
    var varC = horn.makeVariable("c");
    var varD = horn.makeVariable("d");

    var varE = intf.makeVariable("e");
    var n1 = intf.makeNumber(1);


    var clause1 = horn.makeHornClause(varA, jList(varB, varC), intf.greaterOrEquals(varE, n1));
    var clause11 = horn.makeHornClause(varA, jList(), intf.greaterThan(varE, n1));
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
    final var context = SolverContextFactory.createSolverContext(Solvers.ELDARICA);

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

  private HornProverEnvironment solveSmtLib2(final String file) throws Exception {
    var input =
        new String(HornExampleTest.class.getResourceAsStream("/org/sosy_lab/java_smt/test/horn/" + file +
            ".smt2").readAllBytes());

    final var context = SolverContextFactory.createSolverContext(Solvers.ELDARICA);

    var formula = context.getFormulaManager();
    var constraints = formula.parseAll(input);

    var prover = context.newHornProverEnvironment();

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


  private <A> java.util.List<A> jList(A... vars) {
    return java.util.Arrays.asList(vars);
  }
}
