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

import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

// TODO VERY IMPRTNT : rid this class off sysout; take them ALL out; better branch out Debug
// Sessions
public class StpNativeApiTest {

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

  @Ignore
  @Test
  public void testStpGitVersion() throws Exception {
    String version_sha = StpJavaApi.get_git_version_sha();
    System.out.println("\nSHA of this STP version is :");
    System.out.println(version_sha);

    String version_tag = StpJavaApi.get_git_version_tag();
    System.out.println("\nThis STP version is :");
    System.out.println(version_tag);
  }

  @Ignore
  @Test
  public void testStpCompilationEnvironment() throws Exception {
    String compile_env = StpJavaApi.get_compilation_env();
    System.out.println("\nCompilation Environment of this STP version is :");

    System.out.println(compile_env);
  }

  @Ignore // ITS JOB IS DONE; DELETE IT
  @Test
  public void extendedFunctions() {
    // int result = StpJavaApi.extraFunctionSum(100, 50);
    Expr expr = StpJavaApi.vc_trueExpr(stpContextVC);
    String result = StpJavaApi.getType(expr).name();
    System.out.println("result is " + result);
    StpJavaApi.extraSumUpto(10);
    System.out.println("Number of Assertion " + StpJavaApi.getNumOfAsserts(stpContextVC) + "\n");
    StpJavaApi.getSomePrinting(stpContextVC);
    System.out.println("GOOD MORALS: " + StpJavaApi.getSomeXter(stpContextVC) + "\n");
  }

  @Ignore
  @Test
  public void testStpSampleFromRepo() throws Exception {

    int width = 8;

    // Register a callback for errors
    // StpJavaApi.vc_registerErrorHandler(errorHandler);

    // Create variable "x"
    Expr x = StpJavaApi.vc_varExpr(stpContextVC, "x", StpJavaApi.vc_bvType(stpContextVC, width));

    // Create bitvector x + x
    Expr xPlusx = StpJavaApi.vc_bvPlusExpr(stpContextVC, width, x, x);

    // Create bitvector constant 2
    Expr two = StpJavaApi.vc_bvConstExprFromInt(stpContextVC, width, 2);

    // Create bitvector 2*x
    Expr xTimes2 = StpJavaApi.vc_bvMultExpr(stpContextVC, width, two, x);

    // Create bool expression x + x = 2*x
    Expr equality = StpJavaApi.vc_eqExpr(stpContextVC, xPlusx, xTimes2);

    StpJavaApi.vc_assertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));

    // We are asking STP: ∀ x. true → ( x + x = 2*x )
    // This should be VALID.
    System.out.println("######First Query\n");
    handleQuery(stpContextVC, equality);

    // We are asking STP: ∀ x. true → ( x + x = 2 )
    // This should be INVALID.
    System.out.println("######Second Query\n");
    // Create bool expression x + x = 2
    Expr badEquality = StpJavaApi.vc_eqExpr(stpContextVC, xPlusx, two);
    handleQuery(stpContextVC, badEquality);
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

  @Ignore
  @Test
  public void createBooleanVariable_() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar", boolType);
    Expr boolVar2 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType);
    // assertNotEquals(-1, StpJavaApi.vc_isBool(boolVar));

    System.out.println("\n\n ######  ----TYPE INFOR------  ########");
    System.out.println(StpJavaApi.typeString(boolType));

    // type of the expr BOOLEAN
    System.out.println(StpJavaApi.typeString(StpJavaApi.vc_getType(stpContextVC, boolVar)));
    // kind of the expr - SYMBOL
    System.out.println(StpJavaApi.getExprKind(boolVar));

    Expr eqExpr = StpJavaApi.vc_eqExpr(stpContextVC, boolVar, boolVar);
    System.out.println(StpJavaApi.getExprKind(eqExpr));

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);
    Expr eqExpr2 = StpJavaApi.vc_eqExpr(stpContextVC, boolVar, trueExpr);
    System.out.println(StpJavaApi.getExprKind(eqExpr2));
    System.out.println("EXPR KIND for trueExpr - " + StpJavaApi.getExprKind(trueExpr));

    // Always check with getExprKind if expr == SYMBOL
    System.out.println(StpJavaApi.exprName(boolVar));
    // System.out.println(StpJavaApi.exprName(eqExpr)); //Raises an exception

    System.out.println("Equqlity Result - " + StpJavaApi.vc_query(stpContextVC, eqExpr));

    // This will raise exception since eqExpr2 is ill-formed
    // because trueExpr is not a valid Term rather a value while boolVar ia a term
    // System.out.println("Equality Result - " + StpJavaApi.vc_query(stpContextVC, eqExpr2));

    Expr expr1 = StpJavaApi.vc_andExpr(stpContextVC, boolVar, trueExpr);
    Expr expr2 = StpJavaApi.vc_andExpr(stpContextVC, boolVar, boolVar2);
    Expr eqExpr3 = StpJavaApi.vc_eqExpr(stpContextVC, boolVar, expr1);

    Expr andExpr = StpJavaApi.vc_andExpr(stpContextVC, boolVar, eqExpr3);
    System.out.println("Evaluation Result expr1 - " + StpJavaApi.vc_query(stpContextVC, expr1));
    System.out.println("Evaluation Result eqExpr3 - " + StpJavaApi.vc_query(stpContextVC, eqExpr3));
    System.out.println("Evaluation Result andExpr - " + StpJavaApi.vc_query(stpContextVC, andExpr));
    System.out.println("EXPR KIND for expr1 - " + StpJavaApi.getExprKind(expr1));
    System.out.println("EXPR KIND for expr2 - " + StpJavaApi.getExprKind(expr2));
    // System.out.println("IF expr2 is a SYMBOL, it has a name: " + StpJavaApi.exprName(expr2));
    // //Error - non symbol
    // assertEquals(boolType, StpJavaApi.vc_getType(vc, boolVar));
  }

  @Test
  public void createBooleanVariable() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar", boolType);

    assertEquals("BOOLEAN", StpJavaApi.typeString(boolType).trim());
    assertEquals(exprkind_t.SYMBOL, StpJavaApi.getExprKind(boolVar));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, boolVar));
  }

  @Test
  public void validateNotOnBooleanValues() {
    Expr checkforFalseValue =
        StpJavaApi.vc_notExpr(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));
    Expr checkforTrueValue =
        StpJavaApi.vc_notExpr(stpContextVC, StpJavaApi.vc_falseExpr(stpContextVC));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, checkforFalseValue));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, checkforTrueValue));
  }

  @Test
  public void validateAndOnBooleanValues() {
    Expr trueANDfalse =
        StpJavaApi.vc_andExpr(
            stpContextVC,
            StpJavaApi.vc_trueExpr(stpContextVC),
            StpJavaApi.vc_falseExpr(stpContextVC));
    Expr trueANDtrue =
        StpJavaApi.vc_andExpr(
            stpContextVC,
            StpJavaApi.vc_trueExpr(stpContextVC),
            StpJavaApi.vc_trueExpr(stpContextVC));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, trueANDfalse));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, trueANDtrue));
  }

  @Test
  public void validateOrOnBooleanValues() {
    Expr falseORfalse =
        StpJavaApi.vc_orExpr(
            stpContextVC,
            StpJavaApi.vc_falseExpr(stpContextVC),
            StpJavaApi.vc_falseExpr(stpContextVC));
    Expr trueORfalse =
        StpJavaApi.vc_orExpr(
            stpContextVC,
            StpJavaApi.vc_trueExpr(stpContextVC),
            StpJavaApi.vc_falseExpr(stpContextVC));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, falseORfalse));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, trueORfalse));
  }

  @Ignore
  @Test(expected = RuntimeException.class)
  public void validateEqualityOnBooleanValues() {
    Expr falseORfalse =
        StpJavaApi.vc_eqExpr(
            stpContextVC,
            StpJavaApi.vc_falseExpr(stpContextVC),
            StpJavaApi.vc_falseExpr(stpContextVC));
    Expr trueORfalse =
        StpJavaApi.vc_eqExpr(
            stpContextVC,
            StpJavaApi.vc_trueExpr(stpContextVC),
            StpJavaApi.vc_falseExpr(stpContextVC));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, falseORfalse));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, trueORfalse));

    // assertThrows(RuntimeException.class,()->{ StpJavaApi.vc_query_with_timeout(stpContextVC,
    // trueORfalse, 1, 360);} );
    // assertEquals(1, StpJavaApi.vc_query_with_timeout(stpContextVC, trueORfalse, 1, 3));

  }

  @Ignore
  @Test
  public void validateEqualityOnBooleanFormula1() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar", boolType);
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar);

    Expr falseEQtrue = StpJavaApi.vc_eqExpr(stpContextVC, boolVar, notboolVar);
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, falseEQtrue));
  }

  @Test
  public void validateEqualityOnBooleanFormula2() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar", boolType); // false
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar);

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);

    Expr expr1 = StpJavaApi.vc_andExpr(stpContextVC, boolVar, trueExpr); // false
    Expr expr2 = StpJavaApi.vc_andExpr(stpContextVC, notboolVar, notboolVar); // true

    Expr boolVarEQexpr1 = StpJavaApi.vc_eqExpr(stpContextVC, boolVar, expr1);
    Expr notboolVarEQexpr2 = StpJavaApi.vc_eqExpr(stpContextVC, notboolVar, expr2);

    assertEquals(1, StpJavaApi.vc_query(stpContextVC, boolVarEQexpr1));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, notboolVarEQexpr2));
  }

  @Ignore // TODO DEBUG THIS
  @Test(expected = RuntimeException.class)
  public void validateEqualityOnBooleanFormulaGivesException() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType);
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar);

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);

    Expr expr1 = StpJavaApi.vc_andExpr(stpContextVC, boolVar, trueExpr); // false
    Expr expr2 = StpJavaApi.vc_andExpr(stpContextVC, notboolVar, notboolVar); // <- bug here

    // The two Expression Formulae must have the same type.
    assertEquals(type_t.BOOLEAN_TYPE, StpJavaApi.getType(expr1));
    assertEquals(type_t.BOOLEAN_TYPE, StpJavaApi.getType(expr2));

    assertEquals(
        "BOOLEAN", StpJavaApi.typeString(StpJavaApi.vc_getType(stpContextVC, expr1)).trim());
    assertEquals(
        "BOOLEAN", StpJavaApi.typeString(StpJavaApi.vc_getType(stpContextVC, expr2)).trim());

    Expr expr1EQexpr2 = StpJavaApi.vc_eqExpr(stpContextVC, expr1, expr2);

    assertEquals(1, StpJavaApi.vc_query(stpContextVC, expr1EQexpr2)); // <-exception raised here

    // STP itself exits (i guess). So no way round it
    /*
     * Fatal Error: TransformTerm: Illegal kind: You have input a nonterm: 499:(NOT 498:boolVar2) 39
     */
  }

  @Test
  public void validateXor() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType); // false
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar); // true

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);
    Expr falseExpr = StpJavaApi.vc_falseExpr(stpContextVC);

    Expr shouldBeTrue1 = StpJavaApi.vc_xorExpr(stpContextVC, boolVar, notboolVar);
    Expr shouldBeTrue2 = StpJavaApi.vc_xorExpr(stpContextVC, trueExpr, falseExpr);
    Expr shouldBeFalse1 = StpJavaApi.vc_xorExpr(stpContextVC, falseExpr, falseExpr);
    Expr shouldBeFalse2 = StpJavaApi.vc_xorExpr(stpContextVC, notboolVar, notboolVar);

    assertEquals(1, StpJavaApi.vc_query(stpContextVC, shouldBeTrue1));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, shouldBeTrue2));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, shouldBeFalse1));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, shouldBeFalse2));
  }

  @Test
  public void validateIfonlyIf() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType); // false
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar); // true

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);
    Expr falseExpr = StpJavaApi.vc_falseExpr(stpContextVC);

    Expr shouldBeFalse1 = StpJavaApi.vc_iffExpr(stpContextVC, boolVar, notboolVar);
    Expr shouldBeFalse2 = StpJavaApi.vc_iffExpr(stpContextVC, trueExpr, falseExpr);
    Expr shouldBeTrue1 = StpJavaApi.vc_iffExpr(stpContextVC, falseExpr, falseExpr);
    Expr shouldBeTrue2 = StpJavaApi.vc_iffExpr(stpContextVC, notboolVar, notboolVar);

    assertEquals(1, StpJavaApi.vc_query(stpContextVC, shouldBeTrue1));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, shouldBeTrue2));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, shouldBeFalse1));
    assertEquals(0, StpJavaApi.vc_query(stpContextVC, shouldBeFalse2));
  }

  @Test
  public void validateIfThenElse_BoolOnly() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar1 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar1", boolType); // false
    Expr boolVar2 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType); // false
    // Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar1);// true

    Expr trueExpr = StpJavaApi.vc_trueExpr(stpContextVC);
    Expr falseExpr = StpJavaApi.vc_falseExpr(stpContextVC);

    Expr shouldBeboolVar1 = StpJavaApi.vc_iteExpr(stpContextVC, trueExpr, boolVar1, boolVar2);
    Expr shouldBeboolVar2 = StpJavaApi.vc_iteExpr(stpContextVC, falseExpr, boolVar1, boolVar2);

    assertEquals("boolVar1", StpJavaApi.exprName(shouldBeboolVar1));
    assertEquals("boolVar2", StpJavaApi.exprName(shouldBeboolVar2));

    // TODO: extend test for:
    // validateIfThenElse_BVOnly
    // validateIfThenElse_BoolAndBV
  }

  @Ignore // because it stops the tests
  @Test(expected = RuntimeException.class) // This exception cannot be caught the STP lib exits
  public void validateIfThenElse_ConditionNotBool_Exception() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Type bv32Type = StpJavaApi.vc_bv32Type(stpContextVC);

    Expr boolVar1 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar1", boolType); // false
    Expr boolVar2 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar2", boolType); // false
    Expr bv32Var = StpJavaApi.vc_varExpr(stpContextVC, "bv32Var", bv32Type);

    Expr shouldBeboolVar1 = StpJavaApi.vc_iteExpr(stpContextVC, bv32Var, boolVar1, boolVar2);

    assertEquals("boolVar1", StpJavaApi.exprName(shouldBeboolVar1));
  }

  @Test
  public void createBitVectVariables() {
    int numOfBits = 8;
    Type bvType = StpJavaApi.vc_bvType(stpContextVC, numOfBits);
    Type bv32Type = StpJavaApi.vc_bv32Type(stpContextVC);

    Expr bv8bitVar = StpJavaApi.vc_varExpr(stpContextVC, "bv8bitVar", bvType);
    Expr bv32bitVar = StpJavaApi.vc_varExpr(stpContextVC, "bv32bitVar", bv32Type);

    assertEquals(exprkind_t.SYMBOL, StpJavaApi.getExprKind(bv8bitVar));
    assertEquals(exprkind_t.SYMBOL, StpJavaApi.getExprKind(bv32bitVar));

    assertEquals("bv8bitVar", StpJavaApi.exprName(bv8bitVar));
    assertEquals("bv32bitVar", StpJavaApi.exprName(bv32bitVar));

    assertEquals(
        "BITVECTOR(00000008)",
        StpJavaApi.typeString(StpJavaApi.vc_getType(stpContextVC, bv8bitVar)).trim());

    assertEquals(
        "BITVECTOR(00000020)",
        StpJavaApi.typeString(StpJavaApi.vc_getType(stpContextVC, bv32bitVar)).trim());

    assertEquals(8, StpJavaApi.vc_getBVLength(stpContextVC, bv8bitVar));
    assertEquals(32, StpJavaApi.vc_getBVLength(stpContextVC, bv32bitVar));
  }

  @Test
  public void convertBoolToBitVector_() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar1 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar1", boolType); // false
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar1); // true

    Expr bvFrom_boolVar1 = StpJavaApi.vc_boolToBVExpr(stpContextVC, boolVar1); // 1
    Expr bvFrom_notboolVar1 = StpJavaApi.vc_boolToBVExpr(stpContextVC, notboolVar);

    Type type1 = StpJavaApi.vc_getType(stpContextVC, bvFrom_boolVar1);
    type_t type2 = StpJavaApi.getType(bvFrom_notboolVar1);

    //    System.out.println("TYPE-1 - " + StpJavaApi.typeString(type1));
    //    System.out.println("TYPE-2 - " + type2.name());
  }

  @Ignore
  @Test
  public void convertBoolToBitVector() {

    Type boolType = StpJavaApi.vc_boolType(stpContextVC);
    Expr boolVar1 = StpJavaApi.vc_varExpr(stpContextVC, "boolVar1", boolType); // false
    Expr notboolVar = StpJavaApi.vc_notExpr(stpContextVC, boolVar1); // true

    Expr bvFrom_boolVar1 = StpJavaApi.vc_boolToBVExpr(stpContextVC, boolVar1);
    Expr bvFrom_notboolVar1 = StpJavaApi.vc_boolToBVExpr(stpContextVC, notboolVar);

    Expr oneBVconst = StpJavaApi.vc_bv32ConstExprFromInt(stpContextVC, 1);
    Expr zeroBVconst = StpJavaApi.vc_bv32ConstExprFromInt(stpContextVC, 0);
    // Expr zeroBVconst = StpJavaApi.vc_bvConstExprFromStr(stpContextVC, "0");

    // int width = 32;
    // Expr x = StpJavaApi.vc_varExpr(stpContextVC, "x", StpJavaApi.vc_bvType(stpContextVC, width));
    // // Create bitvector one*x
    // Expr xTimesOne = StpJavaApi.vc_bvMultExpr(stpContextVC, width, oneBVconst, x);
    // Expr xTimesBv1 = StpJavaApi.vc_bvMultExpr(stpContextVC, width, bvFrom_boolVar1, x);
    //
    // // Create bitvector zero*x
    // Expr xTimesZero = StpJavaApi.vc_bvMultExpr(stpContextVC, width, zeroBVconst, x);
    // Expr xTimesBv2 = StpJavaApi.vc_bvMultExpr(stpContextVC, width, bvFrom_notboolVar1, x);

    Expr equality1 = StpJavaApi.vc_eqExpr(stpContextVC, oneBVconst, bvFrom_boolVar1);
    Expr equality2 = StpJavaApi.vc_eqExpr(stpContextVC, zeroBVconst, bvFrom_notboolVar1);

    assertEquals(1, StpJavaApi.vc_query(stpContextVC, equality1));
    assertEquals(1, StpJavaApi.vc_query(stpContextVC, equality2));

    // TODO : what does these do:
    // StpJavaApi.vc_assertFormula(stpContextVC, StpJavaApi.vc_trueExpr(stpContextVC));

    // Print the assertions
    // System.out.println("Assertions:\n");
    // StpJavaApi.vc_printAsserts(handle, 0);

  }

  // TODO Extend test: vc_arrayType, vc_paramBoolExpr

  @Test
  public void createArrayVariable() {

    // vc_arrayType(VC vc, Type typeIndex, Type typeData);
    // index type and data type must both be of bitvector (bv) type.
  }

  // vc_isBool -BAD

}
