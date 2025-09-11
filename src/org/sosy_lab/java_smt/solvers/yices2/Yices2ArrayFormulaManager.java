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

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_function_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_lambda;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_variable;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_update;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public class Yices2ArrayFormulaManager
    extends AbstractArrayFormulaManager<Integer, Integer, Long, Integer> {

  /**
   * Cache with constant array values.
   *
   * <p>Used in {@link #internalMakeArray(FormulaType, FormulaType, Integer)} to guarantee that
   * existing constant array values are never re-created
   */
  private final Table<Integer, Integer, Integer> constCache = HashBasedTable.create();

  public Yices2ArrayFormulaManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Integer select(Integer pArray, Integer pIndex) {
    return yices_application(pArray, 1, new int[] {pIndex});
  }

  @Override
  protected Integer store(Integer pArray, Integer pIndex, Integer pValue) {
    return yices_update(pArray, 1, new int[] {pIndex}, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Integer internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    var yicesFuncType =
        yices_function_type(1, new int[] {toSolverType(pIndexType)}, toSolverType(pElementType));
    return ((Yices2FormulaCreator) getFormulaCreator()).createNamedVariable(yicesFuncType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Integer internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, Integer defaultElement) {
    var arraySort = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    if (constCache.contains(arraySort, defaultElement)) {
      return constCache.get(arraySort, defaultElement);
    } else {
      var constant =
          yices_lambda(1, new int[] {yices_new_variable(toSolverType(pIndexType))}, defaultElement);
      constCache.put(arraySort, defaultElement, constant);
      return constant;
    }
  }

  @Override
  protected Integer equivalence(Integer pArray1, Integer pArray2) {
    return yices_eq(pArray1, pArray2);
  }
}
