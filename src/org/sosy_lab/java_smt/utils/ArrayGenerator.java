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

package org.sosy_lab.java_smt.utils;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

public class ArrayGenerator {

  public static <
      TE extends Formula,
      FTE extends FormulaType<TE>> String checkArrayElementSort(FTE pElementType) {
    if (pElementType.isIntegerType()) {
      return  "Int";
    } else if (pElementType.isBooleanType()) {
      return "Bool";
    } else {
      return pElementType + "is not available yet in ArrayGenerator as "
          + "values for Arrays";
    }
  }

  public static <
      TI extends Formula,
      FTI extends FormulaType<TI>> String checkArrayIndexSort(FTI pIndexType) {
    if (pIndexType.isIntegerType()) {
      return  "Int";
    } else if (pIndexType.isBooleanType()) {
      return "Bool";
    } else {
      return pIndexType + "is not available yet in ArrayGenerator as "
          + "index for Arrays";
    }
  }

  public static <
      TI extends Formula,
      TE extends Formula,
      FTI extends FormulaType<TI>,
      FTE extends FormulaType<TE>> void logMakeArray(ArrayFormula result,
                                                                           String pName, FTI pIndexType, FTE pElementType) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pName);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    RecursiveString newEntry = new RecursiveString(result, inputParams, saveResult, "Array");
    newEntry.setArrayIndexType(checkArrayIndexSort(pIndexType));
    newEntry.setArrayValueType(checkArrayElementSort(pElementType));
    Generator.executedAggregator.add(newEntry);
  }

  public static <TI extends Formula, TE extends Formula> void logArrayEquivalence(Object result,
                                                                       ArrayFormula<TI, TE> pArray1, ArrayFormula<TI,
      TE> pArray2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray1);
    inputParams.add(pArray2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) +")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static <TI extends Formula, TE extends Formula> void logSelect(Object result,
                                                                      ArrayFormula<TI,
                                                                 TE> pArray, TI pIndex) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray);
    inputParams.add(pIndex);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(select " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) +")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static <TI extends Formula, TE extends Formula> void logStore(
      Object result, ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pArray);
    inputParams.add(pIndex);
    inputParams.add(pValue);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(store " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + inPlaceInputParams.get(2) +")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  //TODO: getElementType?
  //TODO: getIndexType?

}
