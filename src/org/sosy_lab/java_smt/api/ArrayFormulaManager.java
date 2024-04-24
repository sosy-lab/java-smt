// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;

/**
 * This interface represents the theory of (arbitrarily nested) arrays. (as defined in the SMTLIB2
 * standard)
 */
@SuppressWarnings("MethodTypeParameterName")
public interface ArrayFormulaManager {

  /**
   * Read a value that is stored in the array at the specified position.
   *
   * @param pArray The array from which to read
   * @param pIndex The position from which to read
   * @return A formula that represents the result of the "read"
   */
  <TI extends Formula, TE extends Formula> TE select(ArrayFormula<TI, TE> pArray, TI pIndex);

  /**
   * Store a value into a cell of the specified array.
   *
   * @param pArray The array to which to write
   * @param pIndex The position to which to write
   * @param pValue The value that should be written
   * @return A formula that represents the "write"
   */
  <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue);

  /**
   * Declare a new array with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   *
   * @param pIndexType The type of the array index
   * @param pElementType The type of the array elements
   */
  <TI extends Formula, TE extends Formula, FTI extends FormulaType<TI>, FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType);

  /**
   * Declare a new array with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   *
   * @param type The type of the array, consisting of index type and element type
   */
  default <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> type) {
    return makeArray(pName, type.getIndexType(), type.getElementType());
  }

  /**
   * Create a new array constant with values initialized to elseElem.
   *
   * @param elseElem The default value of all entries in the array.
   */
  <TI extends Formula, TE extends Formula, FTI extends FormulaType<TI>, FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE elseElem);

  /**
   * Create a new array constant with values initialized to elseElem.
   *
   * @param elseElem The default value of all entries in the array.
   */
  default <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      ArrayFormulaType<TI, TE> type, TE elseElem) {
    return makeArray(type.getIndexType(), type.getElementType(), elseElem);
  }

  /** Make a {@link BooleanFormula} that represents the equality of two {@link ArrayFormula}. */
  <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2);

  <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray);

  <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray);
}
