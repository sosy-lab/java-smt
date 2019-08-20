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

public class StpFormulaCreator extends FormulaCreator<Expr, Type, VC, Long> {

  private final VC vc;

  protected StpFormulaCreator(VC vc) {
    super(vc, StpJavaApi.vc_boolType(vc), null, null);
    this.vc = vc;
  }

  @Override
  public Type getBitvectorType(int pBitwidth) {
    return StpJavaApi.vc_bvType(vc, pBitwidth);
  }

  @Override
  public Type getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException("STP does not support FLoating Point yet");
  }

  @Override
  public Type getArrayType(Type pIndexType, Type pElementType) {
    checkArgument(
        StpJavaApi.typeString(pIndexType).contains("BITVECTOR"),
        "ElementType must be a BITVECTOR");
    checkArgument(
        StpJavaApi.typeString(pElementType).contains("BITVECTOR"),
        "ElementType must be a BITVECTOR");

    return StpJavaApi.vc_arrayType(vc, pIndexType, pElementType);
  }

  @Override
  public Expr makeVariable(Type pType, String pVarName) {
    String alphaNum_ = "^[a-zA-Z0-9_]*$";
    checkArgument(
        pVarName.matches(alphaNum_),
        "A valid Variable Name can only contain Alphanumeric and underscore");

    return StpJavaApi.vc_varExpr(vc, pVarName, pType);
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {

    switch (StpJavaApi.getType(pFormula)) {
      case BOOLEAN_TYPE:
        return FormulaType.BooleanType;
      case BITVECTOR_TYPE:
        int bvTypeSize = StpJavaApi.getBVLength(pFormula);
        return FormulaType.getBitvectorTypeWithSize(bvTypeSize);
      case ARRAY_TYPE:

        // STP always use BitVector Type
        int arrayIndexBitWidth = StpJavaApi.getIWidth(pFormula);
        int arrayValueBitWidth = StpJavaApi.getVWidth(pFormula);

        return FormulaType.getArrayType(
            FormulaType.getBitvectorTypeWithSize(arrayValueBitWidth),
            FormulaType.getBitvectorTypeWithSize(arrayIndexBitWidth));

      // TODO Resolve this issue https://github.com/stp/stp/issues/333
      // STP always use a BitVector Type to recreate the type get the ValueBitWidth
      // and IndexBitWidth of the Expr i.e getIWidth and getVWidth

      case UNKNOWN_TYPE:
        throw new IllegalArgumentException("Unknown formula type ");
    }
    return null;

  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Expr pF) {
    // TODO I still don't get what this function is trying to do
    // TODO implement this
    // get the Expr kind for the term
    // ...
    // return null;
    throw new UnsupportedOperationException("Not yet Implemented");
  }

  @Override
  public Expr callFunctionImpl(Long pDeclaration, List<Expr> pArgs) {
    // TODO what is this function doing
    // return null;
    throw new UnsupportedOperationException("Not yet Implemented");
  }

  @Override
  public Long declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {

    // if pArgTypes is empty then use pReturnType an pName to create a variable
    // else ...?!
    // TODO Find out about UF
    // return null;
    throw new UnsupportedOperationException("Not yet Implemented");
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Expr pTFormulaInfo) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Object convertValue(Expr pF) {
    // TODO Auto-generated method stub
    return null;
  }

  /*
   * returns true if the Formula is a value and not an expression
   */
  public boolean isValue() {
    //TODO return if the KIND of Expression is not SYMBOL
    return false;
  }


}
