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

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class UFGenerator {

  protected static String checkUFInputType(ImmutableList<FormulaType<?>> args) {
    StringBuilder inputArgs = new StringBuilder("(");
    for (FormulaType<?> arg : args) {
      if (arg.isArrayType()) {
        inputArgs
            .append("(Array ")
            .append(checkUFOutputType(((ArrayFormulaType<?, ?>) arg).getIndexType()))
            .append(" ")
            .append(checkUFOutputType(((ArrayFormulaType<?, ?>) arg).getElementType()))
            .append(")");
      } else if (arg.isBitvectorType()) {
        inputArgs.append("(_ BitVec ").append(((BitvectorType) arg).getSize()).append(")");
      } else if (arg.isBooleanType()) {
        inputArgs.append("Bool");
      } else if (arg.isIntegerType()) {
        inputArgs.append("Int");
      } else if (arg.isRationalType()) {
        inputArgs.append("Real");
      } else {
        throw new GeneratorException(arg + " is not a known sort. ");
      }
    }
    inputArgs.append(")");
    return String.valueOf(inputArgs);
  }

  protected static String checkUFOutputType(FormulaType<?> out) {
    if (out.isArrayType()) {
      return "(Array "
          + checkUFOutputType(((ArrayFormulaType<?, ?>) out).getIndexType())
          + " "
          + checkUFOutputType(((ArrayFormulaType<?, ?>) out).getElementType())
          + ")";
    } else if (out.isBitvectorType()) {
      return "(_ BitVec " + ((FormulaType.BitvectorType) out).getSize() + ")";
    } else if (out.isBooleanType()) {
      return "Bool";
    } else if (out.isIntegerType()) {
      return "Int";
    } else if (out.isRationalType()) {
      return "Real";
    } else {
      throw new GeneratorException(out + " is not a known sort. ");
    }
  }

  protected static <T extends Formula> void logMakeFun(
      Object result, String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    List<Object> inputParams = new ArrayList<>();

    inputParams.add(pName);
    inputParams.add(pReturnType);
    inputParams.add(pArgTypes);
    Function<List<Object>, String> functionToString = inPlaceInputParams -> "(declare-fun " + inPlaceInputParams.get(0) + " (" + inPlaceInputParams.get(1) + ")" + inPlaceInputParams.get(2) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static <T extends Formula> void logCallFun(
      Object result, FunctionDeclaration<T> funcType, List<? extends Formula> pArgs) {

    List<Object> inputParams = new ArrayList<>(pArgs);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append(funcType.getName()).append(" ");
          inPlaceInputParams.forEach(
              (c) -> {
                out.append(c);
                out.append(" ");
              });
          out.deleteCharAt(out.length() - 1);
          if (!inPlaceInputParams.isEmpty()) {
            out.insert(0, "(");
            out.append(")");
          }
          return String.valueOf(out);
        };
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.UFFUN);
    newEntry.setUFName(funcType.getName());
    newEntry.setUFInputType(checkUFInputType(funcType.getArgumentTypes()));
    newEntry.setUFOutputType(checkUFOutputType(funcType.getType()));
    Generator.executedAggregator.add(newEntry);
  }

  protected static <T extends Formula> void logCallFun(
      Object result, FunctionDeclaration<T> funcType, Formula... args) {

    List<Object> inputParams = new ArrayList<>(Arrays.asList(args));
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append(funcType.getName()).append(" ");
          inPlaceInputParams.forEach(
              (c) -> {
                out.append(c);
                out.append(" ");
              });
          out.deleteCharAt(out.length() - 1);
          if (!inPlaceInputParams.isEmpty()) {
            out.insert(0, "(");
            out.append(")");
          }
          return String.valueOf(out);
        };
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.UFFUN);
    newEntry.setUFName(funcType.getName());
    newEntry.setUFInputType(checkUFInputType(funcType.getArgumentTypes()));
    newEntry.setUFOutputType(checkUFOutputType(funcType.getType()));
    Generator.executedAggregator.add(newEntry);
  }
}
