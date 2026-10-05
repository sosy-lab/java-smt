// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.example.FormulaClassifier;

public class FormulaClassifierTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private FormulaClassifier classifier;

  private static final String BOOL_VARS =
      "(declare-fun x () Bool)" + "(declare-fun foo (Bool) Bool)";

  private static final String NUMERAL_VARS =
      """
      (declare-fun x () Int)\
      (declare-fun xx () Int)\
      (declare-fun y () Real)\
      (declare-fun yy () Real)\
      (declare-fun arr () (Array Int Int))\
      (declare-fun arr2 () (Array Int Int))\
      (declare-fun foo (Int) Int)\
      (declare-fun bar (Real) Real)\
      """;

  private static final String BV_VARS =
      """
      (declare-fun bv () (_ BitVec 4))\
      (declare-fun bv2 () (_ BitVec 4))\
      (declare-fun bvarr () (Array (_ BitVec 4) (_ BitVec 4)))\
      (declare-fun bvarr2 () (Array (_ BitVec 4) (_ BitVec 4)))\
      (declare-fun bvfoo ((_ BitVec 4)) (_ BitVec 4))\
      """;

  @Before
  public void init() {
    requireParser();
    requireVisitor();
    classifier = new FormulaClassifier(context);
  }

  private void requireNonlinear() {
    // OpenSMT and SMTInterpol do not allow nonlinear formulas, even when the solver is not called
    assume()
        .withMessage("Solver %s does not support nonlinear formulas", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.OPENSMT, Solvers.SMTINTERPOL, Solvers.CVC4);
  }

  @Test
  public void test_AUFLIA() {
    requireArrays();
    requireIntegers();
    requireQuantifiers(); // TODO SMTInterpol fails when parsing this
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);
    String query = NUMERAL_VARS + "(assert (exists ((z Int)) (= (select arr x) (foo z))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("AUFLIA");
  }

  @Test
  public void test_QF_AUFLIA() {
    requireArrays();
    requireIntegers();
    String query = NUMERAL_VARS + "(assert (= (select arr x) (foo 0)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFLIA");
  }

  @Test
  public void test_QF_AUFLIRA() {
    // INFO: AUFLIRA only support integers OR reals in OpenSMT
    assume()
        .withMessage("Solver %s does not support mixed integer-real arithmetic", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
    // FIXME: Princess uses quantified variables for the rationals and returns AUFNIRA
    assume()
        .withMessage("Solver %s does not support mixed real-array arithmetic", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    requireArrays();
    requireIntegers();
    requireRationals();
    String query = NUMERAL_VARS + "(assert (= (select arr x) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFLIRA");
  }

  @Test
  public void test_QF_AUFNIRA() {
    // FIXME: Princess uses quantified variables for the rationals and returns AUFNIRA (without the
    //  "QF_" part)
    assume()
        .withMessage("Solver %s does not support mixed real-array arithmetic", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    requireArrays();
    requireIntegers();
    requireRationals();
    requireNonlinear();
    String query = NUMERAL_VARS + "(assert (= (select arr (* x x)) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFNIRA");
  }

  @Test
  public void test_LIA() {
    requireIntegers();
    requireQuantifiers();
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);
    String query = NUMERAL_VARS + "(assert (exists ((z Int)) (= (+ x 1) z)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("LIA");
  }

  @Test
  public void test_LRA() {
    requireRationals();
    requireQuantifiers();
    requireRationals();
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2); // Some solvers rewrite the formula
    String query = NUMERAL_VARS + "(assert (exists ((zz Real)) (= (+ y y) zz)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("LRA");
  }

  @Test
  public void test_LRA_2() {
    requireRationals();
    requireQuantifiers();
    requireRationals();
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2); // Some solvers rewrite the formula
    String query =
        NUMERAL_VARS
            + "(assert (and "
            + "(exists ((a Real) (b Real)) (= (+ y y) (+ a b))) "
            + "(exists ((a Real) (b Real)) (= (+ y y) (- a b))) "
            + "))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("LRA");
  }

  @Test
  public void test_ABVIRA() {
    requireArrays();
    requireQuantifiers();
    requireBitvectors();
    requireIntegers();
    requireRationals();
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);
    String query =
        NUMERAL_VARS
            + BV_VARS
            + "(assert (and (exists ((bv2 (_ BitVec 4))) (= bv bv2)) (= arr arr2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("ABV");
  }

  @Test
  public void test_ABV() {
    requireArrays();
    requireQuantifiers();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);
    String query =
        BOOL_VARS
            + BV_VARS
            + "(assert (and (exists ((bv2 (_ BitVec 4))) (= bv bv2)) (= bvarr "
            + "bvarr2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("ABV");
  }

  @Test
  public void test_QF_AUFBV() {
    requireArrays();
    requireBitvectors();
    String query = BV_VARS + "(assert (and (= bv bv2) (= bvarr bvarr2) (= (bvfoo bv) bv2)" + "))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFBV");
  }

  @Test
  public void test_QF_BV() {
    requireBitvectors();
    // Princess rewrites the formula and replaces the bitvector constant with an integer term
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
    String query = BV_VARS + "(assert (bvult bv (bvadd bv #x1)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_BV");
  }

  @Test
  public void test_QF_LIA() {
    requireIntegers();
    String query = NUMERAL_VARS + "(assert (< xx (* x 2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_LIA");
  }

  @Test
  public void test_QF_LRA() {
    requireRationals();
    String query = NUMERAL_VARS + "(assert (< yy y))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_LRA");
  }

  @Test
  public void test_QF_NIA() {
    requireIntegers();
    requireNonlinear();
    String query = NUMERAL_VARS + "(assert (< xx (* x x)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_NIA");
  }

  @Test
  public void test_QF_NRA() {
    requireRationals();
    requireNonlinear();
    String query = NUMERAL_VARS + "(assert (< yy (* y y)))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_NRA");
  }

  @Test
  public void test_QF_UFLIRA() {
    requireIntegers();
    requireRationals(); // NUMERAL_VARS includes REALs
    String query = NUMERAL_VARS + "(assert (= (foo x) x))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UF");
  }

  @Test
  public void test_QF_UF() {
    String query = BOOL_VARS + "(assert (= (foo x) x))";
    assume()
        .withMessage("MathSAT does not support functions with Bool arguments")
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);
    assume()
        .withMessage("Princess will rewrite UFs with boolean arguments")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UF");
  }

  @Test
  public void test_QF_UFBVLIRA() {
    requireBitvectors();
    requireRationals();
    requireIntegers();
    String query = NUMERAL_VARS + BV_VARS + "(assert (and (= bv bv2) (= (foo x) x)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFBV");
  }

  @Test
  public void test_QF_UFBV() {
    requireBitvectors();
    String query = BV_VARS + "(assert (and (= bv bv2) (= (bvfoo bv) bv2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFBV");
  }

  @Test
  public void test_QF_UFLIRA2() {
    requireIntegers();
    requireRationals(); // NUMERAL_VARS includes REALs
    String query = NUMERAL_VARS + "(assert (< xx (+ x (foo x))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFLIA");
  }

  @Test
  public void test_QF_UFLRA() {
    requireRationals();
    String query = NUMERAL_VARS + "(assert (< yy (bar y)))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFLRA");
  }

  @Test
  public void test_QF_UFNRA() {
    requireRationals();
    requireNonlinear();
    String query = NUMERAL_VARS + "(assert (< (* y yy) (bar y)))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFNRA");
  }

  @Test
  public void test_UFLRA() {
    requireRationals();
    requireQuantifiers();
    String query = NUMERAL_VARS + "(assert (exists ((zz Real)) (< (+ y yy) (bar y))))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("UFLRA");
  }

  @Test
  public void test_UFNRA() {
    requireRationals();
    requireNonlinear();
    requireQuantifiers();
    String query = NUMERAL_VARS + "(assert (exists ((zz Real)) (< (* y yy) (bar y))))";
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.YICES2); // Some solvers rewrite the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("UFNRA");
  }

  @Test
  public void test_QF_FP() {
    requireFloats();
    String query = "(declare-fun a () Float32) (assert (fp.eq a (fp.add RNE a a)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_FP");
  }

  @Test
  public void test_FP() {
    requireFloats();
    requireQuantifiers();
    String query = "(declare-fun a () Float32) (assert (exists ((zz Float32)) (fp.eq a a)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("FP");
  }
}
