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

import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.stp.StpFormula.StpArrayFormula;
import org.sosy_lab.java_smt.solvers.stp.StpFormula.StpBitvectorFormula;
import org.sosy_lab.java_smt.solvers.stp.StpFormula.StpBooleanFormula;

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
        StpJavaApi.typeString(pIndexType).contains("BITVECTOR"), "ElementType must be a BITVECTOR");
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
   * returns true if the Formula is a named variable and not an expression
   */
  public boolean isVariable(Expr expr) {
    exprkind_t kind = StpJavaApi.getExprKind(expr);
    return !kind.equals(exprkind_t.SYMBOL);
  }

  @Override
  protected Expr extractInfo(Formula pT) {
    return StpFormulaManager.getStpTerm(pT);
  }

  @Override
  protected List<Expr> extractInfo(List<? extends Formula> pInput) {
    return Arrays.asList(StpFormulaManager.getStpTerm(pInput));
  }

  @SuppressWarnings("unchecked")
  @Override
  protected <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {

    Expr term = extractInfo(pFormula);
    return (FormulaType<T>) getFormulaType(term);

    // VC vc = getEnv();
    // if (pFormula instanceof BitvectorFormula) {
    // long type = msat_term_get_type(extractInfo(pFormula));
    // checkArgument(
    // msat_is_bv_type(env, type),
    // "BitvectorFormula with actual type " + msat_type_repr(type) + ": " + pFormula);
    // return (FormulaType<T>)
    // FormulaType.getBitvectorTypeWithSize(msat_get_bv_type_size(env, type));
    //
    // } else if (pFormula instanceof FloatingPointFormula) {
    // long type = msat_term_get_type(extractInfo(pFormula));
    // checkArgument(
    // msat_is_fp_type(env, type),
    // "FloatingPointFormula with actual type " + msat_type_repr(type) + ": " + pFormula);
    // return (FormulaType<T>)
    // FormulaType.getFloatingPointType(
    // msat_get_fp_type_exp_width(env, type), msat_get_fp_type_mant_width(env, type));
    // } else if (pFormula instanceof ArrayFormula<?, ?>) {
    // FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
    // FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
    // return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    // }
    // return super.getFormulaType(pFormula);

  }

  @Override
  public BooleanFormula encapsulateBoolean(Expr pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new StpBooleanFormula(pTerm);
  }

  @Override
  protected BitvectorFormula encapsulateBitvector(Expr pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new StpBitvectorFormula(pTerm);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    return new StpArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {

    return ((StpArrayFormula<TI, TE>) pArray).getIndexType();
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {

    return ((StpArrayFormula<TI, TE>) pArray).getElementType();
  }
}
