// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class ArrayGenerator {

  private static String checkArrayElementSort(FormulaType<?> pElementType) {
    if (pElementType.isIntegerType()) {
      return "Int";
    } else if (pElementType.isBooleanType()) {
      return "Bool";
    } else if (pElementType.isRationalType()) {
      return "Real";
    } else if (pElementType.isBitvectorType()) {
      return "(_ BitVec " + ((BitvectorType) pElementType).getSize() + ")";
    } else if (pElementType.isArrayType()) {
      return "(Array "
          + checkArrayIndexSort(((ArrayFormulaType<?, ?>) pElementType).getIndexType())
          + " "
          + checkArrayElementSort(((ArrayFormulaType<?, ?>) pElementType).getElementType())
          + ")";
    } else {
      throw new GeneratorException(
          pElementType + "is not available yet in ArrayGenerator as " + "index for Arrays");
    }
  }

  private static String checkArrayIndexSort(FormulaType<?> pIndexType) {
    if (pIndexType.isIntegerType()) {
      return "Int";
    } else if (pIndexType.isBooleanType()) {
      return "Bool";
    } else if (pIndexType.isRationalType()) {
      return "Real";
    } else if (pIndexType.isBitvectorType()) {
      return "(_ BitVec " + ((BitvectorType) pIndexType).getSize() + ")";
    } else if (pIndexType.isArrayType()) {
      return "(Array "
          + checkArrayIndexSort(((ArrayFormulaType<?, ?>) pIndexType).getIndexType())
          + " "
          + checkArrayElementSort(((ArrayFormulaType<?, ?>) pIndexType).getElementType())
          + ")";
    } else {
      throw new GeneratorException(
          pIndexType + "is not available yet in ArrayGenerator as " + "index for Arrays");
    }
  }

  protected static void logMakeArray(
      ArrayFormula<?, ?> result,
      String pName,
      FormulaType<?> pIndexType,
      FormulaType<?> pElementType) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pName);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.ARRAY);
    newEntry.setArrayIndexType(checkArrayIndexSort(pIndexType));
    newEntry.setArrayValueType(checkArrayElementSort(pElementType));
    Generator.executedAggregator.add(newEntry);
  }

  protected static void logArrayEquivalence(
      Object result, ArrayFormula<?, ?> pArray1, ArrayFormula<?, ?> pArray2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray1);
    inputParams.add(pArray2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logSelect(Object result, ArrayFormula<?, ?> pArray, Formula pIndex) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray);
    inputParams.add(pIndex);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(select " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logStore(
      Object result, ArrayFormula<?, ?> pArray, Formula pIndex, Formula pValue) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray);
    inputParams.add(pIndex);
    inputParams.add(pValue);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(store "
                + inPlaceInputParams.get(0)
                + " "
                + inPlaceInputParams.get(1)
                + " "
                + inPlaceInputParams.get(2)
                + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }
}
