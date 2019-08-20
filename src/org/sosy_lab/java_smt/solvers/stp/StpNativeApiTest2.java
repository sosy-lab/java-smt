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
package org.sosy_lab.java_smt.solvers.stp;

import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class StpNativeApiTest2 {

  private VC stpContextVC;

  @BeforeClass
  public static void loadOpensmt2Library() {
    try {
      NativeLibraries.loadLibrary("stpJapi");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Cannot find at the STP native library", e);
    }
  }

  @Before
  public void createStpVC() {
    stpContextVC = StpJavaApi.vc_createValidityChecker();
  }

  @After
  public void destroyStpVC() {
    StpJavaApi.vc_Destroy(stpContextVC);
  }

  // BITVECTORS
  int width = 8;
  Expr bv_x, bv_xPlusx, two, twenty, xTimes2, xTimes20;
  Expr bv_equality, bv_equality2, bv_non_equality;

  // BOOLEAN
  Expr x1, x2, x3;
  Expr notx1, notx2, notx3;
  Expr x1ORnotx2, notx1ORx2;

  @Test
  public void createBVvariables() {
    // Create variable "x"
    bv_x = StpJavaApi.vc_varExpr(stpContextVC, "x", StpJavaApi.vc_bvType(stpContextVC, width));

    // Create bitvector constant 2
    two = StpJavaApi.vc_bvConstExprFromInt(stpContextVC, width, 2);
    twenty = StpJavaApi.vc_bvConstExprFromInt(stpContextVC, width, 20);

  }

  @Test
  public void createBVformulars() {
    createBVvariables();

    // Create bitvector x + x
    bv_xPlusx = StpJavaApi.vc_bvPlusExpr(stpContextVC, width, bv_x, bv_x); // Non-Formla can't
                                                                           // assert

    // Create bitvector 2*x
    xTimes2 = StpJavaApi.vc_bvMultExpr(stpContextVC, width, two, bv_x); // Non-Formla can't assert
    xTimes20 = StpJavaApi.vc_bvMultExpr(stpContextVC, width, twenty, bv_x); // Non-Formla can't
                                                                            // assert

    // Create bool expression x + x = 2*x
    bv_equality = StpJavaApi.vc_eqExpr(stpContextVC, bv_xPlusx, xTimes2);
    bv_equality2 = StpJavaApi.vc_eqExpr(stpContextVC, bv_xPlusx, xTimes20);

    bv_non_equality = StpJavaApi.vc_notExpr(stpContextVC, bv_equality2);

  }

  @Test
  public void createBOOLvariables() {
    // Create variable "x"
    x1 = StpJavaApi.vc_varExpr(stpContextVC, "x1", StpJavaApi.vc_boolType(stpContextVC));
    x2 = StpJavaApi.vc_varExpr(stpContextVC, "x2", StpJavaApi.vc_boolType(stpContextVC));
    x3 = StpJavaApi.vc_varExpr(stpContextVC, "x3", StpJavaApi.vc_boolType(stpContextVC));
  }

  @Test
  public void createBOOLformulars() {
    createBOOLvariables();

    notx1 = StpJavaApi.vc_notExpr(stpContextVC, x1);
    notx2 = StpJavaApi.vc_notExpr(stpContextVC, x2);
    notx3 = StpJavaApi.vc_notExpr(stpContextVC, x3);

    x1ORnotx2 = StpJavaApi.vc_orExpr(stpContextVC, x1, notx2);
    notx1ORx2 = StpJavaApi.vc_orExpr(stpContextVC, notx1, x2);
  }

  private String evaluateVCqueryResult(int result) {

    if (result == 0) {
      return "INVALID";
    } else if (result == 1) {
      return "VALID";
    } else if (result == 2) {
      return "AN ERROR HAS OCCURED";
    } else if (result == 3) {
      return "TIMEOUT REACHED";
    } else {
      return "UNKNOWN CODE - FATAL ERROR !!!";
    }
  }

  @Test
  public void validBOOLexpr() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);
    Expr frmlr1 = StpJavaApi.vc_andExpr(stpContextVC, term1, notx1ORx2);

    // int result = StpJavaApi.vc_query(stpContextVC, frmlr1); //MYSTERY: why does this gives
    // invalid

    StpJavaApi.addAssertFormula(stpContextVC, frmlr1);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    System.out.println("RESULT IS : " + evaluateVCqueryResult(result));

    // StpJavaApi.vc_printAsserts(stpContextVC, 0);

  }

  StpEnv env;

  void setupStpEnv(VC vc) {
    env = StpJavaApi.createStpEnv(vc);
  }

  @Test
  public void validBOOLeprWithAssert() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);
    StpJavaApi.addAssertFormula(stpContextVC, term1);
    StpJavaApi.addAssertFormula(stpContextVC, notx1ORx2);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    System.out.println("ASSERT RESULT IS : " + evaluateVCqueryResult(result));

  }

  @Test
  public void invalidBOOLexpr1() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);

    StpJavaApi.addAssertFormula(stpContextVC, term1);
    StpJavaApi.addAssertFormula(stpContextVC, notx1);
    StpJavaApi.addAssertFormula(stpContextVC, x2);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    System.out.println("INVALID ASSERT RESULT - 1 IS : " + evaluateVCqueryResult(result)); // VALID

  }

  @Test
  public void invalidBOOLexpr2() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);

    StpJavaApi.addAssertFormula(stpContextVC, term1);
    StpJavaApi.addAssertFormula(stpContextVC, notx1);
    StpJavaApi.addAssertFormula(stpContextVC, x2);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("INVALID ASSERT RESULT - 2 IS : " + evaluateVCqueryResult(result));

    // print counter example
    System.out.println("Counter example:\n");
    StpJavaApi.vc_printCounterExample(stpContextVC);

  }

  @Test
  public void ext_BOOLexpr2() {
    createBOOLvariables();
    createBOOLformulars();
    setupStpEnv(stpContextVC);

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);

    StpJavaApi.ext_push(env);
    StpJavaApi.ext_addFormula(env, term1);
    StpJavaApi.ext_push(env);
    StpJavaApi.ext_addFormula(env, notx1);
    StpJavaApi.ext_push(env);
    StpJavaApi.ext_addFormula(env, x2);

    System.out.println("CACHE size is " + StpJavaApi.getCacheSize(env));
    StpJavaApi.ext_checkSat(env);
  }

  @Test
  public void validBOOLexpr3() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);
    StpJavaApi.push(stpContextVC);
    StpJavaApi.addAssertFormula(stpContextVC, term1);
    StpJavaApi.push(stpContextVC);
    StpJavaApi.addAssertFormula(stpContextVC, notx1);
    // StpJavaApi.push(stpContextVC);
    // StpJavaApi.addAssertFormula(stpContextVC, x2);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("3) INVALID ASSERT RESULT - IS : " + evaluateVCqueryResult(result));
  }

  @Test
  public void pushAndPop_invalidBOOLexpr2() {
    createBOOLvariables();
    createBOOLformulars();

    Expr term1 = StpJavaApi.vc_orExpr(stpContextVC, x1ORnotx2, x3);
    StpJavaApi.push(stpContextVC);
    StpJavaApi.addAssertFormula(stpContextVC, term1);
    StpJavaApi.push(stpContextVC);
    StpJavaApi.addAssertFormula(stpContextVC, notx1);
    StpJavaApi.push(stpContextVC);
    StpJavaApi.addAssertFormula(stpContextVC, x2);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("2) INVALID ASSERT RESULT - IS : " + evaluateVCqueryResult(result));

    // print counter example
    // System.out.println("Counter example:\n");
    // StpJavaApi.vc_printCounterExample(stpContextVC);

    // System.out.println("\n" + "ASSERTS:");
    // StpJavaApi.vc_printAsserts(stpContextVC, 0);

    StpJavaApi.pop(stpContextVC);
    System.out.println("\n" + "AFTER POP 1");
    int result2 = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("2) INVALID ASSERT RESULT - IS : " + evaluateVCqueryResult(result2));

    System.out.println("\n" + "ASSERTS:");
    StpJavaApi.vc_printAsserts(stpContextVC, 0);

    StpJavaApi.pop(stpContextVC);
    System.out.println("\n" + "AFTER POP 2");
    int result3 = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("2) INVALID ASSERT RESULT - IS : " + evaluateVCqueryResult(result3));

    // System.out.println("\n" + "ASSERTS:");
    // StpJavaApi.vc_printAsserts(stpContextVC, 0);

    System.out.println("\n" + "END OF POP TESTING" + "\n");
  }

  @Ignore
  @Test
  public void addAssertionsBV() {

    createBVvariables();
    createBVformulars();

    // StpJavaApi.push(stpContextVC); // Why does this ASSERT (TRUE)
    // StpJavaApi.addAssertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    // StpJavaApi.addAssertFormula(stpContextVC, equality);

    // StpJavaApi.ext_AssertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    // StpJavaApi.ext_AssertFormula(stpContextVC, equality);

    StpJavaApi.addAssertFormula(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));

    // StpJavaApi.vc_printAsserts(stpContextVC, 0);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    System.out.println("RESULT IS : " + result);

    StpJavaApi.vc_printAsserts(stpContextVC, 0);

    // StpJavaApi.checkSAT_old(stpContextVC);
    // StpJavaApi.checkSAT(stpContextVC, notEq);
  }

  @Ignore
  @Test
  public void testingSAT() {
    createBVvariables();
    createBVformulars();

    StpJavaApi.vc_assertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    StpJavaApi.vc_assertFormula(stpContextVC, bv_equality);

    // StpJavaApi.ext_AssertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    // StpJavaApi.ext_AssertFormula(stpContextVC, equality);

    StpJavaApi.extraSumUpto(19);

    int result = StpJavaApi.vc_query(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));

    // Print the assertions
    System.out.println("Assertions: ===>  ");
    StpJavaApi.vc_printAsserts(stpContextVC, 0);
    // System.out.println("\nQuery: ===> ");
    // StpJavaApi.vc_printQuery(stpContextVC);

    System.out.println("VC_QUERY RESULT : ===> " + result);

    StpJavaApi.ext_AssertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));

  }
}