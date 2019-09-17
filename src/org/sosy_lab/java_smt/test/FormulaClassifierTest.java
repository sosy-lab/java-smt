/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.example.FormulaClassifier;

@RunWith(Parameterized.class)
public class FormulaClassifierTest extends SolverBasedTest0 {

  private FormulaClassifier classifier;

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

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Before
  public void init() {
    classifier = new FormulaClassifier(context);
  }

  @Test
  public void test_AUFLIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers(); // TODO SMTInterpol fails when parsing this
    String query = VARS + "(assert (exists ((z Int)) (= (select arr x) (foo z))))";
    classifier.visit(mgr.parse(query));
    assertEquals("AUFLIA", classifier.toString());
  }

  @Test
  public void test_QF_AUFLIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (= (select arr x) (foo 0)))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_AUFLIA", classifier.toString());
  }

  @Test
  public void test_QF_AUFLIRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireRationals();
    String query = VARS + "(assert (= (select arr x) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_AUFLIRA", classifier.toString());
  }

  @Test
  public void test_QF_AUFNIRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireRationals();
    String query = VARS + "(assert (= (select arr (* x x)) (bar (/ 1 2))))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_AUFNIRA", classifier.toString());
  }

  @Test
  public void test_LIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers();
    String query = VARS + "(assert (exists ((z Int)) (= (+ x 1) 0)))";
    classifier.visit(mgr.parse(query));
    assertEquals("LIA", classifier.toString());
  }

  @Test
  public void test_LRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers();
    requireRationals();
    String query = VARS + "(assert (exists ((zz Real)) (= (+ y y) zz)))";
    classifier.visit(mgr.parse(query));
    assertEquals("LRA", classifier.toString());
  }

  @Test
  public void test_ABV() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers();
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query =
        VARS + BVS + "(assert (and (exists ((bv2 (_ BitVec 4))) (= bv bv2)) (= arr arr2)))";
    classifier.visit(mgr.parse(query));
    assertEquals("ABV", classifier.toString());
  }

  @Test
  public void test_QF_AUFBV() {
    // Boolector only supports Bitvectors (bv arrays and ufs) (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireBitvectors();
    // TODO: can i check this with boolector?!
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query = VARS + BVS + "(assert (and (= bv bv2) (= arr arr2) (= (foo x) x)))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_AUFBV", classifier.toString());
  }

  @Test
  public void test_QF_BV() throws SolverException, InterruptedException {
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    // Boolector can't parse formulas, therefore we test it manually
    if (solver == Solvers.BOOLECTOR) {
      BitvectorFormula bv = bvmgr.makeVariable(4, "bv");
      BooleanFormula bvF = bvmgr.lessThan(bv, bvmgr.add(bv, bvmgr.makeBitvector(4, 1)), false);
      assertEquals("QF_BV", classifier.toString());
    } else {
      String query = BVS + "(assert (bvult bv (bvadd bv #x1)))";
      classifier.visit(mgr.parse(query));
      assertEquals("QF_BV", classifier.toString());
    }
  }

  @Test
  public void test_QF_LIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< xx (* x 2)))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_LIA", classifier.toString());
  }

  @Test
  public void test_QF_LRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< yy y))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_LRA", classifier.toString());
  }

  @Test
  public void test_QF_NIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< xx (* x x)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_NIA", classifier.toString());
  }

  @Test
  public void test_QF_NRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< yy (* y y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_NRA", classifier.toString());
  }

  @Test
  public void test_QF_UF() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (= (foo x) x))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_UF", classifier.toString());
  }

  @Test
  public void test_QF_UFBV() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    String query = VARS + BVS + "(assert (and (= bv bv2) (= (foo x) x)))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_UFBV", classifier.toString());
  }

  @Test
  public void test_QF_UFLIA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< xx (+ x (foo x))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_UFLIA", classifier.toString());
  }

  @Test
  public void test_QF_UFLRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< yy (bar y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_UFLRA", classifier.toString());
  }

  @Test
  public void test_QF_UFNRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    String query = VARS + "(assert (< (* y yy) (bar y)))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("QF_UFNRA", classifier.toString());
  }

  @Test
  public void test_UFLRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers();
    String query = VARS + "(assert (exists ((zz Real)) (< (+ y yy) (bar y))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("UFLRA", classifier.toString());
  }

  @Test
  public void test_UFNRA() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireQuantifiers(); // TODO SMTInterpol fails when parsing this
    String query = VARS + "(assert (exists ((zz Real)) (< (* y yy) (bar y))))";
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS); // Princess rewrites the formula
    classifier.visit(mgr.parse(query));
    assertEquals("UFNRA", classifier.toString());
  }

  @Test
  public void test_QF_FP() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireFloats();
    String query = VARS + "(declare-fun a () Float32) (assert (fp.eq a (fp.add RNE a a)))";
    classifier.visit(mgr.parse(query));
    assertEquals("QF_FP", classifier.toString());
  }

  @Test
  public void test_FP() {
    // Boolector only supports Bitvectors (bv arrays and ufs)
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    requireFloats();
    requireQuantifiers();
    String query = VARS + "(declare-fun a () Float32) (assert (exists ((zz Real)) (fp.eq a a)))";
    classifier.visit(mgr.parse(query));
    assertEquals("FP", classifier.toString());
  }
}
