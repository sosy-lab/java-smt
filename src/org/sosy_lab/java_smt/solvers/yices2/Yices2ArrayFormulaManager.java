/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.yices2;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import com.sri.yices.Terms;
import com.sri.yices.Types;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class Yices2ArrayFormulaManager
    extends AbstractArrayFormulaManager<Integer, Integer, Long, Integer> {

  /**
   * Cache with constant array values.
   *
   * <p>Used in {@link #internalMakeArray(FormulaType, FormulaType, Integer)} to guarantee that
   * existing constant array values are never re-created
   */
  private final Table<Integer, Integer, Integer> constCache = HashBasedTable.create();

  Yices2ArrayFormulaManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Integer select(Integer pArray, Integer pIndex) {
    return Terms.funApplication(pArray, pIndex);
  }

  @Override
  protected Integer store(Integer pArray, Integer pIndex, Integer pValue) {
    return Terms.functionUpdate1(pArray, pIndex, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Integer internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    var yicesFuncType = Types.functionType(toSolverType(pIndexType), toSolverType(pElementType));
    return ((Yices2FormulaCreator) getFormulaCreator()).createNamedVariable(yicesFuncType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Integer internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, Integer defaultElement) {
    var arraySort = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    var constantArray = constCache.get(arraySort, defaultElement);
    if (constantArray == null) {
      constantArray =
          Terms.lambda(new int[] {Terms.newVariable(toSolverType(pIndexType))}, defaultElement);
      constCache.put(arraySort, defaultElement, constantArray);
    }
    return constantArray;
  }

  @Override
  protected Integer equivalence(Integer pArray1, Integer pArray2) {
    return Terms.eq(pArray1, pArray2);
  }
}
