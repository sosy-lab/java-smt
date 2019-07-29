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
    super(VC.getCPtr(vc), Type.getCPtr(StpJavaApi.vc_boolType(vc)), null, null);
    this.vc = vc;
  }

  public VC getVC() {
    return vc;
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
    Type indexType = new Type(pIndexType, true);
    Type elementType = new Type(pElementType, true);
    checkArgument(
        StpJavaApi.typeString(indexType).contains("BITVECTOR"),
        "ElementType must be a BITVECTOR");
    checkArgument(
        StpJavaApi.typeString(elementType).contains("BITVECTOR"),
        "ElementType must be a BITVECTOR");

    return Type.getCPtr(StpJavaApi.vc_arrayType(vc, indexType, elementType));
  }

  @Override
  public Long makeVariable(Long pType, String pVarName) {
    String alphaNum_ = "^[a-zA-Z0-9_]*$";
    checkArgument(
        pVarName.matches(alphaNum_),
        "A valid Variable Name can only contain Alphanumeric and underscore");

    return Expr.getCPtr(StpJavaApi.vc_varExpr(vc, pVarName, new Type(pType, true)));
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {

//    long type = msat_term_get_type(pFormula);
//    return getFormulaTypeFromTermType(type);
    // return null;
    Expr formula = new Expr(pFormula, true);
    FormulaType<?> result = null;

    switch (StpJavaApi.getType(formula)) {
      case BOOLEAN_TYPE:
        result = FormulaType.BooleanType;
        break;
      case BITVECTOR_TYPE:
        int bvTypeSize = StpJavaApi.getBVLength(formula);
        result = FormulaType.getBitvectorTypeWithSize(bvTypeSize);
        break;
      case ARRAY_TYPE:
        // get the index type
        // get the element/data type
        // use it to create new Array Type and return it

        // FormulaType.getArrayType(
        // getFormulaTypeFromTermType(indexType),
        // getFormulaTypeFromTermType(elementType));
        // See here:
        // TODO https://github.com/stp/stp/issues/333
        throw new IllegalArgumentException("//TODO implement this for array formula type ");
      case UNKNOWN_TYPE:
        throw new IllegalArgumentException("Unknown formula type ");
    }
    return result;

  }


  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Long pTerm) {
    // TODO implement this
    // get the Expr kind for the term
    // ...

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
