// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_array_const;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_array_read;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_array_write;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

@SuppressWarnings("MethodTypeParameterName")
class Mathsat5ArrayFormulaManager extends AbstractArrayFormulaManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  Mathsat5ArrayFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  @Override
  protected Long select(Long pArray, Long pIndex) {
    return msat_make_array_read(mathsatEnv, pArray, pIndex);
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return msat_make_array_write(mathsatEnv, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final Long mathsatArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return getFormulaCreator().makeVariable(mathsatArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, Long defaultElement) {
    final Long mathsatArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return msat_make_array_const(mathsatEnv, mathsatArrayType, defaultElement);
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return msat_make_equal(mathsatEnv, pArray1, pArray2);
  }
}
