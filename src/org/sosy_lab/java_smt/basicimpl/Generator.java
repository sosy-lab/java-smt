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

package org.sosy_lab.java_smt.basicimpl;

import java.io.IOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class Generator {
  private Generator() {}

  public enum Keyword {
    DIRECT,
    SKIP,
    BOOL,
    INT,
    REAL,
    BITVEC,
    UFFUN,
    ARRAY
  }


  private static boolean loggingEnabled = false;
  private static final String file = "Out.smt2";
  public static final StringBuilder lines = new StringBuilder("(set-logic AUFLIRA)\n");

  public static final List<FunctionEnvironment> executedAggregator = new ArrayList<>();

  public static final List<FunctionEnvironment> registeredVariables = new ArrayList<>();

  protected static void writeToFile(String line, String fileName) throws IOException {

    try {
      try (Writer fileWriter = Files.newBufferedWriter(Paths.get(fileName),
          Charset.defaultCharset())) {
      fileWriter.write(line);
      fileWriter.flush();
      }
    } catch (GeneratorException e) {
      throw new GeneratorException("Could not write to file");
    }
  }

  public static boolean isLoggingEnabled() {
    return loggingEnabled;
  }

  public static void setIsLoggingEnabled(boolean pIsLoggingEnabled) {
    loggingEnabled = pIsLoggingEnabled;
  }

  protected static String evaluateRecursive(Object constraint) {
    if (constraint instanceof String) {
      return (String) constraint;
    } else {
      Optional<FunctionEnvironment> methodToEvaluate =
          executedAggregator.stream().filter(x -> x.getResult().equals(constraint)).findFirst();
      if (methodToEvaluate.isPresent()
          && !methodToEvaluate.get().expressionType.equals(Keyword.DIRECT)) {
        registeredVariables.add(methodToEvaluate.get());
      }
      List<Object> evaluatedInputs = new ArrayList<>();
      for (Object value : Objects.requireNonNull(methodToEvaluate).get().getInputParams()) {
        String evaluatedInput = evaluateRecursive(value);
        evaluatedInputs.add(evaluatedInput);
      }
      return methodToEvaluate.get().getFunctionToString().apply(evaluatedInputs);
    }
  }

  public static void logAddConstraint(BooleanFormula constraint) {
    String result = evaluateRecursive(constraint);
    List<FunctionEnvironment> uniqueRegisteredValues =
        registeredVariables.stream().distinct().collect(Collectors.toList());
    String command = "(assert ";
    for (FunctionEnvironment variable : uniqueRegisteredValues) {
      if (variable.expressionType.equals(Keyword.BOOL)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Bool)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.INT)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Int)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.REAL)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Real)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.BITVEC)) {
        String newEntry =
            "(declare-const "
                + variable.inputParams.get(0)
                + " (_ BitVec "
                + variable.bitVecLength
                + "))\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.ARRAY)) {
        String newEntry =
            "(declare-const "
                + variable.inputParams.get(0)
                + " (Array "
                + variable.arrayIndexType
                + " "
                + variable.arrayValueType
                + "))"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.UFFUN)) {
        String newEntry =
            "(declare-fun "
                + variable.ufName
                + " "
                + variable.ufInputType
                + " "
                + variable.ufOutputType
                + ")"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
    }
    String smtlib2Result = command + result + ")\n";
    lines.append(smtlib2Result);
  }

  protected static void logPop() {
    lines.append("(pop 1)\n");
  }

  protected static void logPush() {
    lines.append("(push 1)\n");
  }

  public static void dumpSMTLIB2() throws IOException {
    String endSMTLIB2 = "(check-sat)\n(get-model)\n(exit)";
    lines.append(endSMTLIB2);
    writeToFile(String.valueOf(lines), file);
    lines.delete(0, lines.length() - 1);
  }
}
