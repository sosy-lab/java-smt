/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.solver.z3java;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FPExpr;
import com.microsoft.z3.FPRMExpr;
import com.microsoft.z3.FPSort;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Sort;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.FloatingPointType;
import org.sosy_lab.solver.basicimpl.AbstractFloatingPointFormulaManager;

import java.math.BigDecimal;

@SuppressFBWarnings("BC_UNCONFIRMED_CAST")
class Z3FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Expr, Sort, Context, FuncDecl> {

  private static final FloatingPointType highPrec = FormulaType.getFloatingPointType(15, 112);

  private final Z3UFManager ufmgr;
  private final Context z3context;

  private final FPRMExpr roundingMode;

  Z3FloatingPointFormulaManager(Z3FormulaCreator creator, Z3UFManager pUFMgr) {
    super(creator);
    z3context = creator.getEnv();
    ufmgr = pUFMgr;
    roundingMode = z3context.mkFPRoundNearestTiesToEven();
  }

  private FPSort mkFPSort(FloatingPointType pType) {
    return (FPSort) getFormulaCreator().getFloatingPointType(pType);
  }

  @Override
  public Expr makeNumberImpl(double pN, FloatingPointType pType) {
    if (Double.isNaN(pN) || Double.isInfinite(pN)) {
      return z3context.mkFP(pN, mkFPSort(pType));
    }
    // Z3 has problems with rounding when giving a double value, so we go via Strings
    return makeNumberImpl(Double.toString(pN), pType);
  }

  @Override
  public Expr makeNumberImpl(BigDecimal pN, FloatingPointType pType) {
    // Using toString() fails in CPAchecker with parse error for seemingly correct strings like
    // "3.4028234663852886E+38" and I have no idea why and cannot reproduce it in unit tests,
    // but toPlainString() seems to work at least.
    return makeNumberImpl(pN.toPlainString(), pType);
  }

  @Override
  protected Expr makeNumberImpl(String pN, FloatingPointType pType) {
    // Z3 does not allow specifying a rounding mode for numerals,
    // so we create it first with a high precision and then round it down explicitly.
    if (pType.getExponentSize() < highPrec.getExponentSize()
        || pType.getMantissaSize() < highPrec.getMantissaSize()) {

      Expr highPrecNumber = z3context.mkNumeral(pN, mkFPSort(highPrec));
      return castToImpl(highPrecNumber, pType).simplify();
    }
    return z3context.mkNumeral(pN, mkFPSort(pType));
  }

  @Override
  public Expr makeVariableImpl(String var, FloatingPointType pType) {
    return getFormulaCreator().makeVariable(mkFPSort(pType), var);
  }

  @Override
  protected Expr makePlusInfinityImpl(FloatingPointType pType) {
    return z3context.mkFPInf(mkFPSort(pType), false);
  }

  @Override
  protected Expr makeMinusInfinityImpl(FloatingPointType pType) {
    return z3context.mkFPInf(mkFPSort(pType), true);
  }

  @Override
  protected Expr makeNaNImpl(FloatingPointType pType) {
    return z3context.mkFPNaN(mkFPSort(pType));
  }

  @Override
  protected Expr castToImpl(Expr pNumber, FormulaType<?> pTargetType) {
    if (pTargetType.isFloatingPointType()) {
      FormulaType.FloatingPointType targetType = (FormulaType.FloatingPointType) pTargetType;
      return z3context.mkFPToFP(roundingMode, (FPExpr) pNumber, mkFPSort(targetType));

    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      return z3context.mkFPToBV(roundingMode, (FPExpr) pNumber, targetType.getSize(), true);

    } else if (pTargetType.isRationalType()) {
      return z3context.mkFPToReal((FPExpr) pNumber);

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  @Override
  protected Expr castFromImpl(Expr pNumber, boolean signed, FloatingPointType pTargetType) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);

    if (formulaType.isFloatingPointType()) {
      return castToImpl(pNumber, pTargetType);

    } else if (formulaType.isBitvectorType()) {
      return z3context.mkFPToFP(roundingMode, (BitVecExpr) pNumber, mkFPSort(pTargetType), signed);

    } else if (formulaType.isRationalType()) {
      return z3context.mkFPToFP(roundingMode, (RealExpr) pNumber, mkFPSort(pTargetType));

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  private Expr genericCast(Expr pNumber, FormulaType<?> pTargetType) {
    Sort argType = pNumber.getSort();
    FuncDecl castFuncDecl =
        ufmgr.declareUninterpretedFunctionImpl(
            "__cast_" + argType + "_to_" + pTargetType,
            toSolverType(pTargetType),
            ImmutableList.of(argType));
    return z3context.mkApp(castFuncDecl, pNumber);
  }

  @Override
  public Expr negate(Expr pNumber) {
    checkArgument(pNumber instanceof FPExpr);
    return z3context.mkFPNeg((FPExpr) pNumber);
  }

  @Override
  public Expr add(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPAdd(roundingMode, (FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr subtract(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPSub(roundingMode, (FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr multiply(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPMul(roundingMode, (FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  protected Expr divide(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPDiv(roundingMode, (FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  protected Expr assignment(Expr pNumber1, Expr pNumber2) {
    return z3context.mkEq(pNumber1, pNumber2);
  }

  @Override
  public Expr equalWithFPSemantics(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPEq((FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr greaterThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPGt((FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr greaterOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPGEq((FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr lessThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPLt((FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  public Expr lessOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkFPLEq((FPExpr) pNumber1, (FPExpr) pNumber2);
  }

  @Override
  protected Expr isNaN(Expr pParam) {
    return z3context.mkFPIsNaN((FPExpr) pParam);
  }

  @Override
  protected Expr isInfinity(Expr pParam) {
    return z3context.mkFPIsInfinite((FPExpr) pParam);
  }

  @Override
  protected Expr isZero(Expr pParam) {
    return z3context.mkFPIsZero((FPExpr) pParam);
  }

  @Override
  protected Expr isSubnormal(Expr pParam) {
    return z3context.mkFPIsSubnormal((FPExpr) pParam);
  }
}
