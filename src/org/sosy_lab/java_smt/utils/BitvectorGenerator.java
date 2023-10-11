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

import static java.lang.Long.parseLong;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class BitvectorGenerator {

  public static void logMakeBitVector(Object result, int length, long i) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(Long.toString(length));
    inputParams.add(Long.toString(i));
    Function<List<Object>, String> saveResult =
        inPlaceInputParamsString -> {
          String formatString = "%0" + (length) + "d";
          int binaryNumber =
              Integer.parseInt(Long.toBinaryString(parseLong((String)inPlaceInputParamsString.get(1))));
          return "#b" + String.format(formatString, binaryNumber);};
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static void logMakeBitVector(BitvectorFormula result, int length, IntegerFormula pI) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(Long.toString(length));
    inputParams.add(pI.toString());
    Function<List<Object>, String> saveResult =
        inPlaceInputParamsString -> {
          String formatString = "%0" + (length) + "d";
          int binaryNumber =
              Integer.parseInt(Long.toBinaryString(parseLong((String)inPlaceInputParamsString.get(1))));
          return "#b" + String.format(formatString, binaryNumber);};
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static void logBVEqual(Object result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= (bvult " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ") (bvult " + inPlaceInputParams.get(1) + " " + inPlaceInputParams.get(0) + "))";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  //TODO LogToIntegerFormula

  public static void logBVNegate(Object result, BitvectorFormula pNumber) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(bvneg " + inPlaceInputParams.get(0) + ")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static void logBVAdd(BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(bvadd " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }
  public static void logBVSub(BitvectorFormula result, BitvectorFormula pNumber1,
                            BitvectorFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(bvsub " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

}
