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

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;

public class UFGenerator <TFormulaInfo, TFunctionDecl, TType, TEnv> {

  public static String checkUFInputType(ImmutableList<FormulaType<?>> args) {
    StringBuilder inputArgs = new StringBuilder("(");
    for (FormulaType arg : args) {
      if (arg.isArrayType()) {
        inputArgs.append("Array");
      } else if (arg.isBitvectorType()) {
        inputArgs.append("BitVec");
      } else if (arg.isBooleanType()) {
        inputArgs.append("Bool");
      } else if (arg.isIntegerType()) {
        inputArgs.append("Int");
      }
    }
    inputArgs.append(")");
    return String.valueOf(inputArgs);
  }

  public static String checkUFOutputType(FormulaType out) {
    if (out.isArrayType()) {
      return "Array";
    } else if (out.isBitvectorType()) {
      return "BitVec";
    } else if (out.isBooleanType()) {
      return "Bool";
    } else if (out.isIntegerType()) {
      return "Int";
    } else {
      return "Type not available yet";
    }
  }

  public static void logMakeSort(Object result, String pName) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pName);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    RecursiveString newEntry = new RecursiveString(result, inputParams, saveResult, "UFSort");
    Generator.executedAggregator.add(newEntry);
  }
  public static <T extends Formula> void logMakeFun(Object result,
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pName);
    inputParams.add(pReturnType);
    inputParams.add(pArgs);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(declare-fun " + inPlaceInputParams.get(0) + " ("  + inPlaceInputParams.get(1) + ")" + inPlaceInputParams.get(2) + ")";
    Generator.executedAggregator.add(new RecursiveString(result, inputParams, saveResult, "Skip"));
  }

  public static <T extends Formula> void logDeclareUF(Object result,
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pName);
    inputParams.add(pReturnType);
    inputParams.add(pArgTypes);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    RecursiveString newEntry = new RecursiveString(result, inputParams, saveResult, "Skip");
    Generator.executedAggregator.add(newEntry);
  }

  public static <T extends Formula> void logCallFun(Object result,
                                                    FunctionDeclaration<T> funcType, Formula... args) {
    StringBuilder out = new StringBuilder();
    out.append("(" + funcType.getName() + " ");
    List<Object> inputParams = new ArrayList<>();
    for (Object pOperand : args) {
      inputParams.add(pOperand);
    }
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          inPlaceInputParams.forEach((c) -> {
            out.append(c);
            out.append(" ");
          });
          return String.valueOf(
              out.deleteCharAt(out.length() - 1).append(")"));
        };
    RecursiveString newEntry = new RecursiveString(result, inputParams, saveResult, "UFFun");
    newEntry.setUFName(funcType.getName());
    newEntry.setUFInputType(checkUFInputType(funcType.getArgumentTypes()));
    newEntry.setUFOutputType(checkUFOutputType(funcType.getType()));
    Generator.executedAggregator.add(newEntry);
  }

  //TODO: logDeclareAndCallUF
}
