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

import static com.google.common.base.Preconditions.checkArgument;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class StpBooleanFormulaManager
    // extends AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> {
    extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {
  private final VC vc;
  protected StpBooleanFormulaManager(StpFormulaCreator pCreator) {
    super(pCreator);

    vc = pCreator.getVC();
  }

  @Override
  protected Long makeVariableImpl(String pVar) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    Expr result = null;
    if (pValue) {
      result = StpJavaApi.vc_trueExpr(vc);
    } else {
      result = StpJavaApi.vc_falseExpr(vc);
    }
    return Expr.getCPtr(result);
  }

  @Override
  protected Long not(Long pParam1) {
    Expr result = StpJavaApi.vc_notExpr(vc, new Expr(pParam1, true));
    return Expr.getCPtr(result);

  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    Expr result = StpJavaApi.vc_andExpr(vc, new Expr(pParam1, true), new Expr(pParam2, true));
    return Expr.getCPtr(result);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    Expr result = StpJavaApi.vc_orExpr(vc, new Expr(pParam1, true), new Expr(pParam2, true));
    return Expr.getCPtr(result);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    Expr result = StpJavaApi.vc_xorExpr(vc, new Expr(pParam1, true), new Expr(pParam2, true));
    return Expr.getCPtr(result);
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {

    Expr expr1 = new Expr(pBits1, true);
    Expr expr2 = new Expr(pBits2, true);

    boolean check = StpJavaApi.getType(expr1).equals(StpJavaApi.getType(expr2));
    checkArgument(check, "STP allows equivalence only for Formulae of the same type");

    Expr result = StpJavaApi.vc_eqExpr(vc, expr1, expr2);
    return Expr.getCPtr(result);
  }

  @Override
  protected boolean isTrue(Long pBits) {

    Expr expr = new Expr(pBits, true);

    exprkind_t result = StpJavaApi.getExprKind(expr);
    switch (result) {
      case TRUE:
        return true;
      case FALSE:
        return false;
      default:
        throw new IllegalArgumentException(
            "In STP solver: Formula of type - " + result + "needs to be SAT checked.");
    }
  }

  /**
   * This function returns false also if Formula is not boolean
   */
  @Override
  protected boolean isFalse(Long pBits) {

    Expr expr = new Expr(pBits, true);

    exprkind_t result = StpJavaApi.getExprKind(expr);
    switch (result) {
      case TRUE:
        return false;
      case FALSE:
        return true;
      default:
        throw new IllegalArgumentException(
            "In STP solver: Formula of type - " + result + "needs to be SAT checked.");
    }
  }

  /***
   * @return either a Bit Vector or Boolean depending on the type of formulas
   * @param pCond must be boolean
   * @param pF1 and @param pF2 must have the same type (Boolean or BitVector)
   *
   */
  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {

    Expr cond = new Expr(pCond, true);
    Expr thenExpr = new Expr(pF1, true);
    Expr elseExpr = new Expr(pF2, true);

    boolean checkConditon = StpJavaApi.getType(cond).equals(type_t.BOOLEAN_TYPE);
    checkArgument(checkConditon, "The conditon for If-Then-Else must be a Boolean type");

    type_t typeThen = StpJavaApi.getType(thenExpr);
    type_t typeElse = StpJavaApi.getType(elseExpr);

    checkArgument(typeThen.equals(typeElse), "Both Then and Else clauses must be of the same type");

    boolean check = typeThen.equals(type_t.BITVECTOR_TYPE) || typeThen.equals(type_t.BOOLEAN_TYPE);
    checkArgument(check, "Both Then and Else clauses must be either of BOOLEAN or BITVECTOR type");


    Expr result =
        StpJavaApi.vc_iteExpr(vc, new Expr(pCond, true), new Expr(pF1, true), new Expr(pF2, true));
    return Expr.getCPtr(result);
  }
}
