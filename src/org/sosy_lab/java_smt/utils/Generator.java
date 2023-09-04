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
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

public class Generator {

  static String fileName = "Out.txt";
  static StringBuilder lines = new StringBuilder();
  //Liste von Ergebnissen auf Eingabeparametern mit executed functions
  static List<Triple<Object, List<Object>, Function<List<Object>, String>>> executedAggregator =
      new ArrayList<Triple<Object, List<Object>, Function<List<Object>, String>>>();

  private static List<String> registeredVariables = new ArrayList();


  public Generator() throws IOException {
    lines.append("(set-logic ALL)\n");
  }

  public static void writeToFile(String line) throws IOException {
    File file = new File(fileName);
    FileWriter fileWriter = new FileWriter(fileName, true);
    fileWriter.write(line);
    fileWriter.close();
  }

  public static String evaluateRecursive(Object constraint) throws IOException {
    var methodToEvaluate = executedAggregator
        .stream()
        .filter(x -> x.getFirst().equals(constraint))
        .findFirst()
        .orElse(null);

    if (constraint instanceof String) {
      var result = (String) constraint;
      registeredVariables.add(result);
      return result;
    } else {
      List<Object> evaluatedInputs = new ArrayList<>();
      for (var value:methodToEvaluate.getSecond()) {
        var evaluatedInput = evaluateRecursive(value);
        evaluatedInputs.add(evaluatedInput);
      }
      var result = methodToEvaluate.getThird().apply(evaluatedInputs);
      return result;
    }

  }

  public static void dumpSMTLIB2(Object constraint) throws IOException {
    var result = evaluateRecursive(constraint);
    List<String> uniqueRegisteredValues =
        registeredVariables.stream().distinct().collect(Collectors.toList());
    for (var variable:uniqueRegisteredValues) {
      writeToFile("(declare-const " + variable + " Bool)\n");
    }
    writeToFile(result);
  }



  public static String saveResult(List<Object> inputParams) {

    return (String) inputParams.get(0);
  }

  //List<Triple<Object, List<Object>, Function<List<Object>, String>>>
  public static void logMakeVariable(Object result, String pVar) {
    String out = "(declare-const " + pVar + " Bool)\n";
    lines.append(out);
    List<Object> temp = new ArrayList<>();
    temp.add(pVar);
    Function<List<Object>, String> saveResult = inputParams -> (String) inputParams.get(0);
    executedAggregator.add(new Triple<Object, List<Object>, Function<List<Object>, String>>(result, temp, saveResult));
  }

  public static void logNot(Object result, BooleanFormula pBits) {
    String out = "(not " + pBits + ")\n";
    lines.append(out);
    List<Object> temp = new ArrayList<>();
    temp.add(pBits);
    Function<List<Object>, String> saveResult = inputParams -> "(not " + (String) inputParams.get(0) + ")";
    executedAggregator.add(new Triple<Object, List<Object>, Function<List<Object>, String>>(result, temp, saveResult));
  }

  public static void logOr(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(or " + pBits1 + " " + pBits2 + ")\n";
    lines.append(out);
    List<Object> temp = new ArrayList<>();
    temp.add(pBits1);
    temp.add(pBits2);
    Function<List<Object>, String> saveResult =
        inputParams -> "(or " + (String) inputParams.get(0) + " " + (String) inputParams.get(1) + ")";
    executedAggregator.add(new Triple<Object, List<Object>, Function<List<Object>, String>>(result, temp, saveResult));
  }

  public static void logAnd(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(assert (and " + pBits1 + " " + pBits2 + "))\n";
    lines.append(out);
  }

  public static void logXor(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(assert (xor " + pBits1 + " " + pBits2 + "))\n";
    lines.append(out);
  }
}
