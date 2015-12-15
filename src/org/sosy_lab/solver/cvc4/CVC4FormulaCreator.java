/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.cvc4;

import edu.nyu.acsys.CVC4.ArrayType;
import edu.nyu.acsys.CVC4.BitVectorType;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.FloatingPointType;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

public class CVC4FormulaCreator extends FormulaCreator<Expr, Type, CVC4Environment> {

  private final ExprManager exprManager;

  protected CVC4FormulaCreator(CVC4Environment pEnv) {
    super(pEnv, pEnv.getExprManager().booleanType(), pEnv.getExprManager().integerType(), null);
    exprManager = pEnv.getExprManager();
  }

  @Override
  public Type getBitvectorType(int pBitwidth) {
    return exprManager.mkBitVectorType(pBitwidth);
  }

  @Override
  public Type getFloatingPointType(FloatingPointType pType) {
    return exprManager.mkFloatingPointType(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  public Type getArrayType(Type pIndexType, Type pElementType) {
    return exprManager.mkArrayType(pIndexType, pElementType);
  }

  @Override
  public Expr makeVariable(Type pType, String pVarName) {
    return exprManager.mkVar(pVarName, pType);
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    Type t = pFormula.getType();
    if (t.isArray()) {
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(((ArrayType) t).getIndexType()),
          getFormulaTypeFromTermType(((ArrayType) t).getBaseType()));
    }
    return getFormulaTypeFromTermType(t);
  }

  private FormulaType<?> getFormulaTypeFromTermType(Type t) {
    if (t.isBoolean()) {
      return FormulaType.BooleanType;
    } else if (t.isInteger()) {
      return FormulaType.IntegerType;
    } else if (t.isBitVector()) {
      return FormulaType.getBitvectorTypeWithSize((int) ((BitVectorType) t).getSize());
    } else if (t.isFloatingPoint()) {
      return FormulaType.getFloatingPointType(
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getExponentSize(),
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getSignificandSize());
    } else {
      throw new AssertionError("Unhandled type " + t.getClass());
    }
  }
}
