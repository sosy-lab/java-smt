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

import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.native_api.stp.Expr;
import org.sosy_lab.java_smt.native_api.stp.VC;
import org.sosy_lab.java_smt.native_api.stp.ifaceflag_t;
import org.sosy_lab.java_smt.native_api.stp.stpJapi;

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
    String version_sha = stpJapi.get_git_version_sha();
    System.out.println("\nSHA of this STP version is :");
    System.out.println(version_sha);

    String version_tag = stpJapi.get_git_version_tag();
    System.out.println("\nThis STP version is :");
    System.out.println(version_tag);

  }

  @Test
  public void testStpCompilationEnvironment() throws Exception {
    String compile_env = stpJapi.get_compilation_env();
    System.out.println("\nCompilation Environment of this STP version is :");

    System.out.println(compile_env);

    // stpJapi.
    ifaceflag_t x = ifaceflag_t.EXPRDELETE;

  }

  @Test
  public void testStpSampleFromRepo() throws Exception {

    int width = 8;

    VC handle = stpJapi.vc_createValidityChecker();

    // Register a callback for errors
    // stpJapi.vc_registerErrorHandler(errorHandler);

    // Create variable "x"
    Expr x = stpJapi.vc_varExpr(handle, "x", stpJapi.vc_bvType(handle, width));

    // Create bitvector x + x
    Expr xPlusx = stpJapi.vc_bvPlusExpr(handle, width, x, x);

    // Create bitvector constant 2
    Expr two = stpJapi.vc_bvConstExprFromInt(handle, width, 2);

    // Create bitvector 2*x
    Expr xTimes2 = stpJapi.vc_bvMultExpr(handle, width, two, x);

    // Create bool expression x + x = 2*x
    Expr equality = stpJapi.vc_eqExpr(handle, xPlusx, xTimes2);

    stpJapi.vc_assertFormula(handle, stpJapi.vc_trueExpr(handle));

    // We are asking STP: ∀ x. true → ( x + x = 2*x )
    // This should be VALID.
    System.out.println("######First Query\n");
    handleQuery(handle, equality);

    // We are asking STP: ∀ x. true → ( x + x = 2 )
    // This should be INVALID.
    System.out.println("######Second Query\n");
    // Create bool expression x + x = 2
    Expr badEquality = stpJapi.vc_eqExpr(handle, xPlusx, two);
    handleQuery(handle, badEquality);

    // Clean up
    stpJapi.vc_Destroy(handle);

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
    stpJapi.vc_printAsserts(handle, 0);

    int result = stpJapi.vc_query(handle, queryExpr);
    System.out.println("Query:\n");
    stpJapi.vc_printQuery(handle);
    switch (result) {
      case 0:
        System.out.println("Query is INVALID\n");

        // print counter example
        System.out.println("Counter example:\n");
        stpJapi.vc_printCounterExample(handle);
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
}

