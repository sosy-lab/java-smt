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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.mk_eq;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.basicimpl.AbstractArrayFormulaManager;

class Z3ArrayFormulaManager extends AbstractArrayFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3ArrayFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected Long select(Long pArray, Long pIndex) {
    return Z3NativeApi.mk_select(z3context, pArray, pIndex);
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return Z3NativeApi.mk_store(z3context, pArray, pIndex, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Long z3ArrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(z3ArrayType, pName);
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return mk_eq(z3context, pArray1, pArray2);
  }
}
