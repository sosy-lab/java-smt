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

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

class StpArrayFormulaManager extends AbstractArrayFormulaManager<Expr, Type, VC, Long> {

  private final VC vc;

  public StpArrayFormulaManager(StpFormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    this.vc = pFormulaCreator.getEnv();
  }

  @Override
  protected Expr select(Expr pArray, Expr pIndex) {
    boolean checkArray = type_t.ARRAY_TYPE.equals(StpJavaApi.getType(pArray));
    checkArgument(checkArray, "Argument not of type ARRAY");
    boolean checkIndex = type_t.BITVECTOR_TYPE.equals(StpJavaApi.getType(pIndex));
    checkArgument(checkIndex, "Argument not of type BITVECTOR");

    return StpJavaApi.vc_readExpr(vc, pArray, pIndex);
  }

  @Override
  protected Expr store(Expr pArray, Expr pIndex, Expr pValue) {
    boolean checkArray = type_t.ARRAY_TYPE.equals(StpJavaApi.getType(pArray));
    checkArgument(checkArray, "Argument not of type ARRAY");
    boolean checkIndex = type_t.BITVECTOR_TYPE.equals(StpJavaApi.getType(pIndex));
    checkArgument(checkIndex, "Argument not of type BITVECTOR");
    boolean checkValue = type_t.BITVECTOR_TYPE.equals(StpJavaApi.getType(pValue));
    checkArgument(checkValue, "Argument not of type BITVECTOR");

    return StpJavaApi.vc_writeExpr(vc, pArray, pIndex, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Expr internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    ArrayFormulaType<TI, TE> arrayFormulaType = FormulaType.getArrayType(pIndexType, pElementType);
    Type stpArrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(stpArrayType, pName);
  }

  @Override
  protected Expr equivalence(Expr pArray1, Expr pArray2) {
    return StpJavaApi.vc_eqExpr(vc, pArray1, pArray2);
  }
}
