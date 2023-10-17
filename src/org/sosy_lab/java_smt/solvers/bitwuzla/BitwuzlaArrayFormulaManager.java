// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), pArray, pIndex);
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final long bitwuzlaArrayType = toSolverType(arrayFormulaType);
    long newVar = getFormulaCreator().makeVariable(bitwuzlaArrayType, pName);
    return newVar;
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL.swigValue(), pArray1, pArray2);
  }
}
