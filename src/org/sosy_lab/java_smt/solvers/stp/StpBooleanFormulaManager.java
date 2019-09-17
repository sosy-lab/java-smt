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

class StpBooleanFormulaManager extends AbstractBooleanFormulaManager<Expr, Type, VC, Long> {

  private final VC vc;

  protected StpBooleanFormulaManager(StpFormulaCreator pCreator) {
    super(pCreator);
    vc = pCreator.getEnv();
  }

  @Override
  protected Expr makeVariableImpl(String pVar) {
    Type boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    Expr result;
    if (pValue) {
      result = StpJavaApi.vc_trueExpr(vc);
    } else {
      result = StpJavaApi.vc_falseExpr(vc);
    }
    return result;
  }

  @Override
  protected Expr not(Expr pParam1) {
    return StpJavaApi.vc_notExpr(vc, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_andExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_orExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_xorExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr equivalence(Expr pBits1, Expr pBits2) {

    boolean check = StpJavaApi.getType(pBits1).equals(StpJavaApi.getType(pBits2));
    checkArgument(check, "STP allows equivalence only for Formulae of the same type");

    return StpJavaApi.vc_eqExpr(vc, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Expr pBits) {
    exprkind_t result = StpJavaApi.getExprKind(pBits);
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

  @Override
  protected boolean isFalse(Expr pBits) {

    exprkind_t result = StpJavaApi.getExprKind(pBits);
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

  @Override
  protected Expr ifThenElse(Expr cond, Expr thenExpr, Expr elseExpr) {

    boolean checkConditon = StpJavaApi.getType(cond).equals(type_t.BOOLEAN_TYPE);
    checkArgument(checkConditon, "The conditon for If-Then-Else must be a Boolean type");

    type_t typeThen = StpJavaApi.getType(thenExpr);
    type_t typeElse = StpJavaApi.getType(elseExpr);

    checkArgument(typeThen.equals(typeElse), "Both Then and Else clauses must be of the same type");

    boolean check = typeThen.equals(type_t.BITVECTOR_TYPE) || typeThen.equals(type_t.BOOLEAN_TYPE);
    checkArgument(check, "Both Then and Else clauses must be either of BOOLEAN or BITVECTOR type");

    return StpJavaApi.vc_iteExpr(vc, cond, thenExpr, elseExpr);
  }
}
