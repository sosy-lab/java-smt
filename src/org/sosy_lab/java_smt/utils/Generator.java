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

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Triple;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class Generator {

  static String fileName = "Out.txt";
  static StringBuilder lines = new StringBuilder();

  /** List of Triples which contain:
   * an object (output of used method)
   * a list of objects (input of used method)
   * a function which takes a list of objects and returns a String
   */
  static List<Triple<Object, List<Object>, Function<List<Object>, String>>> executedAggregator =
      new ArrayList<>();

  private static final List<String> registeredVariables = new ArrayList<>();

  public Generator() throws IOException {
    lines.append("(set-logic ALL)\n");
  }

  public static void writeToFile(String line) throws IOException {
    File file = new File(fileName);
    FileWriter fileWriter = new FileWriter(fileName);
    fileWriter.write(line);
    fileWriter.close();
  }

  public static String evaluateRecursive(Object constraint) {
    Triple<Object, List<Object>, Function<List<Object>, String>> methodToEvaluate = executedAggregator
        .stream()
        .filter(x -> x.getFirst().equals(constraint))
        .findFirst()
        .orElse(null);

    if (constraint instanceof String) {
      String result = (String) constraint;
      registeredVariables.add(result);
      return result;
    } else {
      List<Object> evaluatedInputs = new ArrayList<>();
      for (Object value: Objects.requireNonNull(methodToEvaluate).getSecond()) {
        String evaluatedInput = evaluateRecursive(value);
        evaluatedInputs.add(evaluatedInput);
      }
      String result = methodToEvaluate.getThird().apply(evaluatedInputs);
      return result;
    }
  }

  public static void logAddConstraint(Object constraint) {
    String result = evaluateRecursive(constraint);
    List<String> uniqueRegisteredValues =
        registeredVariables.stream().distinct().collect(Collectors.toList());
    for (String variable:uniqueRegisteredValues) {
      if (! variable.equals("true") && ! variable.equals("false")) {
        String newEntry = "(declare-const " + variable + " Bool)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
    }
    String SMTLIB2Result = "(assert " + result + ")\n";
    lines.append(SMTLIB2Result);
  }

  public static void dumpSMTLIB2() throws IOException {
    String endSMTLIB2 = "(check-sat)\n(exit)";
    lines.append(endSMTLIB2);
    writeToFile(String.valueOf(lines));
  }

  public static String saveResult(List<Object> inputParams) {

    return (String) inputParams.get(0);
  }

  //List<Triple<Object, List<Object>, Function<List<Object>, String>>>
  public static void logMakeVariable(Object result, String pVar) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logMakeTrue(Object result, String pVar) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logMakeFalse(Object result, String pVar) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logNot(Object result, BooleanFormula pBits) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> "(not " + inPlaceInputParams.get(0) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logOr(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(or " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logOr(Object result, Collection<BooleanFormula> pBits1) {
    StringBuilder out = new StringBuilder();
    out.append("(or ");
    List<Object> inputParams = new ArrayList<>();
    Iterator<BooleanFormula> it = pBits1.iterator();
    for (int i = 0; i < pBits1.size(); i++) {
      inputParams.add(it.next());
    }
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          inPlaceInputParams.forEach((c) -> {out.append(c); out.append(" ");}); return String.valueOf(
            out.deleteCharAt(out.length()-1).append(")"));};

    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logAnd(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(and " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logAnd(Object result, Collection<BooleanFormula> pBits1) {
    StringBuilder out = new StringBuilder();
    out.append("(and ");
    List<Object> inputParams = new ArrayList<>();
    Iterator<BooleanFormula> it = pBits1.iterator();
    for (int i = 0; i < pBits1.size(); i++) {
      inputParams.add(it.next());
    }
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          inPlaceInputParams.forEach((c) -> {out.append(c); out.append(" ");}); return String.valueOf(
              out.deleteCharAt(out.length()-1).append(")"));};

    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logXor(Object result,BooleanFormula pBits1, BooleanFormula pBits2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(xor " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logEquivalence(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  public static void logImplication(Object result,BooleanFormula pBits1, BooleanFormula pBits2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(=> " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }

  //TODO: logIsTrue (not necessary?)

  //TODO: logIsFalse (not necessary?)

  public static void logIfThenElse(Object result, BooleanFormula pBits1, Object f1, Object f2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(f1);
    inputParams.add(f2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(ite " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + " " + inPlaceInputParams.get(2) + ")" ;
    executedAggregator.add(new Triple<>(result, inputParams, saveResult));
  }
}
