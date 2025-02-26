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

  @Before
  public void checkNotSolverless() {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SOLVERLESS);
  }

  private static final String VARS =
      "(declare-fun x () Int)"
          + "(declare-fun xx () Int)"
          + "(declare-fun y () Real)"
          + "(declare-fun yy () Real)"
          + "(declare-fun arr () (Array Int Int))"
          + "(declare-fun arr2 () (Array Int Int))"
          + "(declare-fun foo (Int) Int)"
          + "(declare-fun bar (Real) Real)";

  private static final String BVS =
      "(declare-fun bv () (_ BitVec 4))" + "(declare-fun bv2 () (_ BitVec 4))";

  @Before
  public void init() {
    classifier = new FormulaClassifier(context);
  }

  private void requireNonlinear() {
    // INFO: OpenSMT does not allow nonlinear formulas, even when the solver is not called
    assume()
        .withMessage("Solver %s does not support nonlinear formulas", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
  }

  @Test
  public void test_AUFLIA() {
    requireParser();
    requireQuantifiers(); // TODO SMTInterpol fails when parsing this
    String query = VARS + "(assert (exists ((z Int)) (= (select arr x) (foo z))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("AUFLIA");
  }

  @Test
  public void test_QF_AUFLIA() {
    requireParser();
    String query = VARS + "(assert (= (select arr x) (foo 0)))";
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

    requireParser();
    requireRationals();
    String query = VARS + "(assert (= (select arr x) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFLIRA");
  }

  @Test
  public void test_QF_AUFNIRA() {
    requireParser();
    requireRationals();
    requireNonlinear();
    String query = VARS + "(assert (= (select arr (* x x)) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFNIRA");
  }

  @Test
  public void test_LIA() {
    requireParser();
    requireQuantifiers();
    String query = VARS + "(assert (exists ((z Int)) (= (+ x 1) 0)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("LIA");
  }

  @Test
  public void test_LRA() {
    requireParser();
    requireQuantifiers();
    requireRationals();
    String query = VARS + "(assert (exists ((zz Real)) (= (+ y y) zz)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("LRA");
  }

  @Test
  public void test_ABV() {
    requireParser();
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query =
        VARS + BVS + "(assert (and (exists ((bv2 (_ BitVec 4))) (= bv bv2)) (= arr arr2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("ABV");
  }

  @Test
  public void test_QF_AUFBV() {
    requireParser();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query = VARS + BVS + "(assert (and (= bv bv2) (= arr arr2) (= (foo x) x)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_AUFBV");
  }

  @Test
  public void test_QF_BV() {
    requireParser();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query = BVS + "(assert (bvult bv (bvadd bv #x1)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_BV");
  }

  @Test
  public void test_QF_LIA() {
    requireParser();
    String query = VARS + "(assert (< xx (* x 2)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_LIA");
  }

  @Test
  public void test_QF_LRA() {
    requireParser();
    String query = VARS + "(assert (< yy y))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_LRA");
  }

  @Test
  public void test_QF_NIA() {
    requireParser();
    requireNonlinear();
    String query = VARS + "(assert (< xx (* x x)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_NIA");
  }

  @Test
  public void test_QF_NRA() {
    requireParser();
    requireNonlinear();
    String query = VARS + "(assert (< yy (* y y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_NRA");
  }

  @Test
  public void test_QF_UF() {
    requireParser();
    String query = VARS + "(assert (= (foo x) x))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UF");
  }

  @Test
  public void test_QF_UFBV() {
    requireParser();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query = VARS + BVS + "(assert (and (= bv bv2) (= (foo x) x)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFBV");
  }

  @Test
  public void test_QF_UFLIA() {
    requireParser();
    String query = VARS + "(assert (< xx (+ x (foo x))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFLIA");
  }

  @Test
  public void test_QF_UFLRA() {
    requireParser();
    String query = VARS + "(assert (< yy (bar y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFLRA");
  }

  @Test
  public void test_QF_UFNRA() {
    requireParser();
    requireNonlinear();
    String query = VARS + "(assert (< (* y yy) (bar y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_UFNRA");
  }

  @Test
  public void test_UFLRA() {
    requireParser();
    requireQuantifiers();
    String query = VARS + "(assert (exists ((zz Real)) (< (+ y yy) (bar y))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("UFLRA");
  }

  @Test
  public void test_UFNRA() {
    requireParser();
    requireQuantifiers(); // TODO SMTInterpol fails when parsing this
    String query = VARS + "(assert (exists ((zz Real)) (< (* y yy) (bar y))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("UFNRA");
  }

  @Test
  public void test_QF_FP() {
    requireParser();
    requireFloats();
    String query = VARS + "(declare-fun a () Float32) (assert (fp.eq a (fp.add RNE a a)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("QF_FP");
  }

  @Test
  public void test_FP() {
    requireParser();
    requireFloats();
    requireQuantifiers();
    String query = VARS + "(declare-fun a () Float32) (assert (exists ((zz Real)) (fp.eq a a)))";
    classifier.visit(mgr.parse(query));
    assertThat(classifier.toString()).isEqualTo("FP");
  }
}
