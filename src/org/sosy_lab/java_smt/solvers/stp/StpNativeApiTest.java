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

import static org.junit.Assert.assertEquals;

import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class StpNativeApiTest {

  @BeforeClass
  public static void loadOpensmt2Library() {
    try {
      NativeLibraries.loadLibrary("stpJapi");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Cannot find at the STP native library", e);
    }
  }

  @Test
  public void testStpGitVersion() throws Exception {
    String version_sha = StpJavaApi.get_git_version_sha();
    System.out.println("\nSHA of this STP version is :");
    System.out.println(version_sha);

    String version_tag = StpJavaApi.get_git_version_tag();
    System.out.println("\nThis STP version is :");
    System.out.println(version_tag);

  }

  @Test
  public void testStpCompilationEnvironment() throws Exception {
    String compile_env = StpJavaApi.get_compilation_env();
    System.out.println("\nCompilation Environment of this STP version is :");

    System.out.println(compile_env);

    // StpJavaApi.
    ifaceflag_t x = ifaceflag_t.EXPRDELETE;

  }

  @Test
  public void testStpSampleFromRepo() throws Exception {

    int width = 8;

    VC handle = StpJavaApi.vc_createValidityChecker();

    // Register a callback for errors
    // StpJavaApi.vc_registerErrorHandler(errorHandler);

    // Create variable "x"
    Expr x = StpJavaApi.vc_varExpr(handle, "x", StpJavaApi.vc_bvType(handle, width));

    // Create bitvector x + x
    Expr xPlusx = StpJavaApi.vc_bvPlusExpr(handle, width, x, x);

    // Create bitvector constant 2
    Expr two = StpJavaApi.vc_bvConstExprFromInt(handle, width, 2);

    // Create bitvector 2*x
    Expr xTimes2 = StpJavaApi.vc_bvMultExpr(handle, width, two, x);

    // Create bool expression x + x = 2*x
    Expr equality = StpJavaApi.vc_eqExpr(handle, xPlusx, xTimes2);

    StpJavaApi.vc_assertFormula(handle, StpJavaApi.vc_trueExpr(handle));

    // We are asking STP: ∀ x. true → ( x + x = 2*x )
    // This should be VALID.
    System.out.println("######First Query\n");
    handleQuery(handle, equality);

    // We are asking STP: ∀ x. true → ( x + x = 2 )
    // This should be INVALID.
    System.out.println("######Second Query\n");
    // Create bool expression x + x = 2
    Expr badEquality = StpJavaApi.vc_eqExpr(handle, xPlusx, two);
    handleQuery(handle, badEquality);

    // Clean up
    StpJavaApi.vc_Destroy(handle);

  }

  // void handleQuery(VC handle, Expr queryExpr);

  // Error handler
  void errorHandler(String err_msg) throws Exception {
    System.out.printf("Error: %s\n", err_msg);
    throw new Exception(err_msg);
  }

  void handleQuery(VC handle, Expr queryExpr) {
    // Print the assertions
    System.out.println("Assertions:\n");
    StpJavaApi.vc_printAsserts(handle, 0);

    int result = StpJavaApi.vc_query(handle, queryExpr);
    System.out.println("Query:\n");
    StpJavaApi.vc_printQuery(handle);
    switch (result) {
      case 0:
        System.out.println("Query is INVALID\n");

        // print counter example
        System.out.println("Counter example:\n");
        StpJavaApi.vc_printCounterExample(handle);
        break;

      case 1:
        System.out.println("Query is VALID\n");
        break;
      case 2:
        System.out.println("Could not answer query\n");
        break;
      case 3:
        System.out.println("Unhandled error\n");
    }
    System.out.println("\n\n");
  }

  @Test
  public void createBooleanVariable() {

    // create STP context
    VC vc = StpJavaApi.vc_createValidityChecker();

    Type boolType = StpJavaApi.vc_boolType(vc);
    Expr boolVar = StpJavaApi.vc_varExpr(vc, "boolVar", boolType);
    // assertNotEquals(-1, StpJavaApi.vc_isBool(boolVar));

    assertEquals(boolType, StpJavaApi.vc_getType(vc, boolVar));

    // Clean up STP context
    StpJavaApi.vc_Destroy(vc);

  }

  // vc_varExpr
  // vc_isBool
  // vc_arrayType
  // vc_bvType
  // vc_trueExpr
  // vc_falseExpr
  // vc_notExpr
  // vc_andExpr
  // vc_orExpr
  // vc_xorExpr
  // vc_eqExpr
  // vc_iffExpr
  // vc_iteExpr

}

