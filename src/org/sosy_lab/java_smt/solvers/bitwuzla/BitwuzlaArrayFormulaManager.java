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

import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_EQUAL;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

public class BitwuzlaArrayFormulaManager
    extends AbstractArrayFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {

  protected BitwuzlaArrayFormulaManager(BitwuzlaFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Long select(Long pArray, Long pIndex) {
    return bitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), pArray, pIndex);
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return bitwuzlaJNI.bitwuzla_mk_term3(
        BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), pArray, pIndex, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    // Maybe use FormulaCache if tests fail
    //    Long maybeFormula = formulaCache.get(pName, pIndexType);
    //    if (maybeFormula != null) {
    //      return maybeFormula;
    //    }
    //    if (formulaCache.containsRow(pName)) {
    //      throw new IllegalArgumentException("Symbol already used: " + pName);
    //    }

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final long bitwuzlaArrayType = toSolverType(arrayFormulaType);
    long newVar = getFormulaCreator().makeVariable(bitwuzlaArrayType, pName);
    // formulaCache.put(pName, pIndexType, newVar);
    return newVar;
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL.swigValue(), pArray1, pArray2);
  }
}
