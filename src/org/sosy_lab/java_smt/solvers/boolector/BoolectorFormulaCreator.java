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
package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBitvectorFormula;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorFormula.BoolectorBooleanFormula;

public class BoolectorFormulaCreator
    extends FormulaCreator<Long, Long, BoolectorEnvironment, Long> {

  BoolectorFormulaCreator(BoolectorEnvironment pEnv) {
    super(pEnv, pEnv.getBoolSort(), null, null);
  }

  // sehr unfertig und temporär
  // TODO gescheit!!!!
  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    long btor = getEnv().getBtor();
    if (pFormula instanceof BitvectorFormula) {
      long sort = BtorJNI.boolector_get_sort(btor, extractInfo(pFormula));
      checkArgument(
          BtorJNI.boolector_is_bitvec_sort(btor, sort),
          "BitvectorFormula with type missmatch: " + pFormula);
      return (FormulaType<T>) FormulaType
          .getBitvectorTypeWithSize((int) BtorJNI.boolector_get_width(btor, extractInfo(pFormula)));

    } /*
       * else if (pFormula instanceof ) { // TODO UF? }
       */ else if (pFormula instanceof ArrayFormula<?, ?>) {
      // TODO ARRAY
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public Long extractInfo(Formula pT) {
    return BoolectorFormulaManager.getBtorTerm(pT);
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long btor = getEnv().getBtor();
    long sort = BtorJNI.boolector_get_sort(btor, pFormula);
    if (BtorJNI.boolector_is_bitvec_sort(btor, sort)) {
      if (sort == 1) {
        return FormulaType.BooleanType;
      } else {
        return FormulaType
            .getBitvectorTypeWithSize((int) BtorJNI.boolector_get_width(btor, pFormula));
      }
    } else if (BtorJNI.boolector_is_array_sort(btor, sort)) {
      int indexWidth = (int) BtorJNI.boolector_get_index_width(btor, pFormula);
      int elementWidth = (int) BtorJNI.boolector_get_width(btor, pFormula);
      return FormulaType.getArrayType(
          FormulaType.getBitvectorTypeWithSize(indexWidth),
          FormulaType.getBitvectorTypeWithSize(elementWidth));
    }
    throw new IllegalArgumentException("Unknown formula type for " + pFormula);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm)) : String
        .format("Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new BoolectorBooleanFormula(
          pTerm); /*
                   * } else if (pType.isArrayType()) { ArrayFormulaType<?, ?> arrFt =
                   * (ArrayFormulaType<?, ?>) pType; return (T) new BoolectorArrayFormula<>(pTerm,
                   * arrFt.getIndexType(), arrFt.getElementType());
                   */
    } else if (pType.isBitvectorType()) {
      return (T) new BoolectorBitvectorFormula(pTerm);
    }
    throw new IllegalArgumentException(
        "Cannot create formulas of type " + pType + " in Boolector.");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new BoolectorBooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new BoolectorBitvectorFormula(pTerm);
  }

  // TODO encapsulate remaining types

  // In Boolector a type is called a sort
  @Override
  public Long getBitvectorType(int pBitwidth) {
    return BtorJNI.boolector_bitvec_sort(getEnv().getBtor(), pBitwidth);
  }

  @Override
  public Long getFloatingPointType(FloatingPointType pType) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    return BtorJNI.boolector_array_sort(getEnv().getBtor(), pIndexType, pElementType);
  }

  @Override
  public Long makeVariable(Long pType, String pVarName) {
    return BtorJNI.boolector_var(getEnv().getBtor(), pType, pVarName);
  }

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
