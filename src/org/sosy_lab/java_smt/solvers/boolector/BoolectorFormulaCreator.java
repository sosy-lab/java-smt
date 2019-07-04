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

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BoolectorFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  protected BoolectorFormulaCreator(
      Long pEnv,
      Long pBoolType,
      @Nullable Long pIntegerType,
      @Nullable Long pRationalType) {
    super(pEnv, pBoolType, pIntegerType, pRationalType);
    // TODO Auto-generated constructor stub
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long type = msat_term_get_type(pFormula);
    return getFormulaTypeFromTermType(type);
  }

  private FormulaType<?> getFormulaTypeFromTermType(Long type) {
    long env = getEnv();
    if (msat_is_bool_type(env, type)) {
      return FormulaType.BooleanType;
    } else if (msat_is_integer_type(env, type)) {
      return FormulaType.IntegerType;
    } else if (msat_is_rational_type(env, type)) {
      return FormulaType.RationalType;
    } else if (msat_is_bv_type(env, type)) {
      return FormulaType.getBitvectorTypeWithSize(msat_get_bv_type_size(env, type));
    } else if (msat_is_fp_type(env, type)) {
      return FormulaType.getFloatingPointType(
          msat_get_fp_type_exp_width(env, type),
          msat_get_fp_type_mant_width(env, type));
    } else if (msat_is_fp_roundingmode_type(env, type)) {
      return FormulaType.FloatingPointRoundingModeType;
    } else if (msat_is_array_type(env, type)) {
      long indexType = msat_get_array_index_type(env, type);
      long elementType = msat_get_array_element_type(env, type);
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(indexType),
          getFormulaTypeFromTermType(elementType));
    }
    throw new IllegalArgumentException("Unknown formula type " + msat_type_repr(type));
  }

  @Override
  public Long getBitvectorType(int pBitwidth) {
    return msat_get_bv_type(getEnv(), pBitwidth);
  }

}
