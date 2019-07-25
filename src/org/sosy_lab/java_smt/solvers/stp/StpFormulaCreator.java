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

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

//extends FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> {
public class StpFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  // protected StpFormulaCreator(
  // Long pEnv,
  // Long pBoolType,
  // @Nullable Long pIntegerType,
  // @Nullable Long pRationalType) {
  // super(pEnv, pBoolType, null, null);
  //
  // }
  //
  // protected StpFormulaCreator(Long pEnv) {
  // super(pEnv, StpJavaApi.vc_boolType(vc), null, null);
  //
  // }

  // protected StpFormulaCreator(StpEnvironment pEnviron) {
  //
  // }

  private final VC vc;

  protected StpFormulaCreator(VC vc) {
    super(StpVC.getVCptr(vc), Type.getCPtr(StpJavaApi.vc_boolType(vc)), null, null);
    this.vc = vc;
  }


  @Override
  public Long getBitvectorType(int pBitwidth) {
    return Type.getCPtr(StpJavaApi.vc_bvType(vc, pBitwidth));
  }

  @Override
  public Long getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException("STP does not support FLoating Point yet");
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    return Type.getCPtr(
        StpJavaApi.vc_arrayType(vc, new Type(pIndexType, true), new Type(pElementType, true)));
  }

  @Override
  public Long makeVariable(Long pType, String pVarName) {
    String alphaNum_ = "^[a-zA-Z0-9_]*$";
    assert (pVarName
        .matches(alphaNum_)) : "A valid Variable Name can only contain Alphanumeric and underscore";
    return Expr.getCPtr(StpJavaApi.vc_varExpr(vc, pVarName, new Type(pType, true)));
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    System.out.println("I came here.");
//    long type = msat_term_get_type(pFormula);
//    return getFormulaTypeFromTermType(type);
    return null;
  }

  /*
   * private FormulaType<?> getFormulaTypeFromTermType(Long type) { // long env = getEnv(); if
   * (msat_is_bool_type(env, type)) { return FormulaType.BooleanType; } else if
   * (msat_is_integer_type(env, type)) { return FormulaType.IntegerType; } else if
   * (msat_is_rational_type(env, type)) { return FormulaType.RationalType; } else if
   * (msat_is_bv_type(env, type)) { return
   * FormulaType.getBitvectorTypeWithSize(msat_get_bv_type_size(env, type)); } else if
   * (msat_is_fp_type(env, type)) { return FormulaType.getFloatingPointType(
   * msat_get_fp_type_exp_width(env, type), msat_get_fp_type_mant_width(env, type)); } else if
   * (msat_is_fp_roundingmode_type(env, type)) { return FormulaType.FloatingPointRoundingModeType; }
   * else if (msat_is_array_type(env, type)) { long indexType = msat_get_array_index_type(env,
   * type); long elementType = msat_get_array_element_type(env, type); return
   * FormulaType.getArrayType( getFormulaTypeFromTermType(indexType),
   * getFormulaTypeFromTermType(elementType)); } throw new
   * IllegalArgumentException("Unknown formula type " + msat_type_repr(type)); }
   */
  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Long pF) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long callFunctionImpl(Long pDeclaration, List<Long> pArgs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long declareUFImpl(String pName, Long pReturnType, List<Long> pArgTypes) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pTFormulaInfo) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Object convertValue(Long pF) {
    // TODO Auto-generated method stub
    return null;
  }

}
