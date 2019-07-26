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
    // Expr result = StpJavaApi.vc_eqExpr(vc, new Expr(pBits1, true), new Expr(pBits2, true));

    // if and only if
    Expr result = StpJavaApi.vc_iffExpr(vc, new Expr(pBits1, true), new Expr(pBits2, true));

    return Expr.getCPtr(result);
  }

  @Override
  protected boolean isTrue(Long pBits) {

    int result = StpJavaApi.vc_isBool(new Expr(pBits, true));
    if (result == 1) {
      return true;
    } else {
      return false;
    }
    // else if (result == 0) {
    // return false;
    // }else { //-1 is not boolean
    // throw new Exception("The Formaula is not boolean");
    // }
  }

  @Override
  protected boolean isFalse(Long pBits) {
    int result = StpJavaApi.vc_isBool(new Expr(pBits, true));
    if (result == 0) {
      return true;
    } else {
      return false;
    }
  }

  /***
   * @return either a Bit Vector or Boolean depending on the type of formulas
   * @param pCond must be boolean
   * @param pF1 and @param pF2 must have the same type
   *
   */
  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    // TODO Enforce the rules stated in the doc comment above
    Expr result =
        StpJavaApi.vc_iteExpr(vc, new Expr(pCond, true), new Expr(pF1, true), new Expr(pF2, true));
    return Expr.getCPtr(result);
  }
}
