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
package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

public class CVC4FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  protected CVC4FloatingPointFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getEnv();
  }

  @Override
  protected Expr getDefaultRoundingMode() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeNumberImpl(
      double pN, FloatingPointType pType, Expr pFloatingPointRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeNumberImpl(
      BigDecimal pN, FloatingPointType pType, Expr pFloatingPointRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeNumberImpl(
      String pN, FloatingPointType pType, Expr pFloatingPointRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeVariableImpl(String varName, FloatingPointType pType) {
    long pExponentSize = pType.getExponentSize();
    long pMantissaSize = pType.getMantissaSize();
    Type type = exprManager.mkFloatingPointType(pExponentSize, pMantissaSize);
    return exprManager.mkVar(varName, type);
  }

  @Override
  protected Expr makePlusInfinityImpl(FloatingPointType pType) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeMinusInfinityImpl(FloatingPointType pType) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeNaNImpl(FloatingPointType pType) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr castToImpl(Expr pNumber, FormulaType<?> pTargetType, Expr pRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr castFromImpl(
      Expr pNumber, boolean pSigned, FloatingPointType pTargetType, Expr pRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_NEG, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_PLUS, pParam1, pParam2);
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2, Expr pFloatingPointRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_SUB, pParam1, pParam2);
  }

  @Override
  protected Expr divide(Expr pParam1, Expr pParam2, Expr pFloatingPointRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_DIV, pParam1, pParam2);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2, Expr pFloatingPointRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_MULT, pParam1, pParam2);
  }

  @Override
  protected Expr assignment(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr equalWithFPSemantics(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_EQ, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_GT, pParam1, pParam2);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_GEQ, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_LT, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_LEQ, pParam1, pParam2);
  }

  @Override
  protected Expr isNaN(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISNAN, pParam1);
  }

  @Override
  protected Expr isInfinity(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISINF, pParam1);
  }

  @Override
  protected Expr isZero(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISZ, pParam1);
  }

  @Override
  protected Expr isSubnormal(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISSN, pParam1);
  }

  @Override
  protected Expr fromIeeeBitvectorImpl(Expr pNumber, FloatingPointType pTargetType) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr toIeeeBitvectorImpl(Expr pNumber) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr round(Expr pFormula, FloatingPointRoundingMode pRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr isNormal(Expr pParam) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr isNegative(Expr pParam) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }
}
