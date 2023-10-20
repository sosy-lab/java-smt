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

package org.sosy_lab.java_smt.utils.Generators;


import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class Generator {

  static String fileName = "Out.smt2";
  public static StringBuilder lines = new StringBuilder();

  static List<RecursiveString> executedAggregator =
      new ArrayList<>();

  private static final List<RecursiveString> registeredVariables = new ArrayList<>();

  public Generator() throws IOException {
    lines.append("(set-logic AUFLIRA)\n");
  }

  public static void writeToFile(String line) throws IOException {
    File file = new File(fileName);
    FileWriter fileWriter = new FileWriter(fileName);
    fileWriter.write(line);
    fileWriter.close();
  }

  public static String evaluateRecursive(Object constraint) {
    RecursiveString methodToEvaluate = executedAggregator
        .stream()
        .filter(x -> x.getResult().equals(constraint))
        .findFirst()
        .orElse(null);
    if (methodToEvaluate != null && ! methodToEvaluate.variableType.equals("Direct")) {
      registeredVariables.add(methodToEvaluate);
    }

    if (constraint instanceof String) {
      String result = (String) constraint;
      return result;
    } else {
      List<Object> evaluatedInputs = new ArrayList<>();
      for (Object value: Objects.requireNonNull(methodToEvaluate).getInputParams()) {
        String evaluatedInput = evaluateRecursive(value);
        evaluatedInputs.add(evaluatedInput);
      }
      String result = (String) methodToEvaluate.getSaveResult().apply(evaluatedInputs);
      return result;
    }
  }

  public static void logAddConstraint(BooleanFormula constraint) {
    String result = evaluateRecursive(constraint);
    List<RecursiveString> uniqueRegisteredValues =
        registeredVariables.stream().distinct().collect(Collectors.toList());
    String command = "(assert ";
    for (RecursiveString variable : uniqueRegisteredValues) {
      if (variable.variableType.equals("Bool")) {
        String newEntry = "(declare-const " + variable.result + " Bool)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
      if (variable.variableType.equals("Int")) {
        String newEntry = "(declare-const " + variable.result + " Int)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
      if (variable.variableType.equals("BitVec")) {
        String newEntry =
            "(declare-const " + variable.result + " (_ BitVec " + variable.bitVecLength + "))\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
      if (variable.variableType.equals("Array")) {
        String newEntry =
            "(declare-const " + variable.result + " (Array " + variable.ArrayIndexType + " "
                + variable.ArrayValueType + "))"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
      if (variable.variableType.equals("UFSort")) {
        System.out.println(variable.result);
        String newEntry =
            "(declare-sort " + variable.result + " 0)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
      if (variable.variableType.equals("UFFun")) {
        System.out.println(variable.result);
        String newEntry =
            "(declare-fun " + variable.UFName + " " + variable.UFInputType + " " + variable.UFOutputType + ")"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        } else {
        }
      }
    }
    String SMTLIB2Result = command + result + ")\n";
    lines.append(SMTLIB2Result);
  }

  public static void dumpSMTLIB2() throws IOException {
    String endSMTLIB2 = "(exit)";
    lines.append(endSMTLIB2);
    writeToFile(String.valueOf(lines));
  }

}
