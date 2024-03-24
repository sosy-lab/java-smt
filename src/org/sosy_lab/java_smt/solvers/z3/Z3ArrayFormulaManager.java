// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

class Z3ArrayFormulaManager extends AbstractArrayFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3ArrayFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected Long select(Long pArray, Long pIndex) {
    return Native.mkSelect(z3context, pArray, pIndex);
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return Native.mkStore(z3context, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Long z3ArrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(z3ArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    long func =
        getFormulaCreator()
            .declareUFImpl(
                "__unnamed_arr", toSolverType(pElementType), List.of(toSolverType(pIndexType)));
    return Native.mkAsArray(z3context, func);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      Long elseElem, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    return Native.mkConstArray(z3context, toSolverType(pIndexType), elseElem);
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return Native.mkEq(z3context, pArray1, pArray2);
  }
}
