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


package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.microsoft.z3.Native;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

public class BitwuzlaFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {
  protected BitwuzlaFormulaCreator(
      Long pLong,
      Long boolType,
      @Nullable Long pIntegerType,
      @Nullable Long pRationalType,
      @Nullable Long stringType,
      @Nullable Long regexType) {
    super(pLong, boolType, pIntegerType, pRationalType, stringType, regexType);
  }

  @Override
  public Long getBitvectorType(int bitwidth) {
    return null;
  }

  // Assuming that JavaSMT FLoatingPointType follows IEEE 754, if it is in the decimal
  // system instead use bitwuzla_mk_fp_value_from_real somehow or convert myself
  @Override
  public Long getFloatingPointType(FloatingPointType type) {
    long fpSort = BitwuzlaJNI.bitwuzla_mk_fp_sort(getEnv(), type.getExponentSize(),
        type.getMantissaSize());
    return fpSort;
  }

  @Override
  public Long getArrayType(Long indexType, Long elementType) {
    return null;
  }

  @Override
  public Long makeVariable(Long pLong, String varName) {
    return null;
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    return null;
  }

  /**
   * @param visitor
   * @param formula
   * @param f
   * @see FormulaManager#visit
   */
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long f) {
    return null;
  }

  @Override
  public Long callFunctionImpl(Long declaration, List<Long> args) {
    return null;
  }

  @Override
  public Long declareUFImpl(String pName, Long pReturnType, List<Long> pArgTypes) {
    return null;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    return null;
  }
}
