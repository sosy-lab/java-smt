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
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;

public class UFGenerator <TFormulaInfo, TFunctionDecl, TType, TEnv> {

  public static String checkUFInputType(ImmutableList<FormulaType<?>> args) {
    StringBuilder inputArgs = new StringBuilder("(");
    for (FormulaType arg : args) {
      if (arg.isArrayType()) {
        inputArgs.append("Array");
      } else if (arg.isBitvectorType()) {
        inputArgs.append("(_ BitVec " + ((FormulaType.BitvectorType) arg).getSize() + ")");
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
      return "(_ BitVec " + ((FormulaType.BitvectorType) out).getSize() + ")";
    } else if (out.isBooleanType()) {
      return "Bool";
    } else if (out.isIntegerType()) {
      return "Int";
    } else {
      return "Type not available yet";
    }
  }

  public static <T extends Formula> void logMakeFun(Object result,
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    List<Object> inputParams = new ArrayList<>();

    inputParams.add(pName);
    inputParams.add(pReturnType);
    inputParams.add(pArgTypes);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(declare-fun " + inPlaceInputParams.get(0) + " ("  + inPlaceInputParams.get(1) + ")" + inPlaceInputParams.get(2) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }


  public static <T extends Formula> void logCallFun(Object result,
                                                    FunctionDeclaration<T> funcType, List<? extends Formula> pArgs) {

    List<Object> inputParams = new ArrayList<>();
    inputParams.addAll(pArgs);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append(funcType.getName() + " ");
          inPlaceInputParams.forEach((c) -> {
            out.append(c);
            out.append(" ");
          });
          out.deleteCharAt(out.length()-1);
          if (inPlaceInputParams.size() > 0) {
            out.insert(0, "(");
            out.append(")");
          }
          return String.valueOf(out);
        };
    RecursiveString newEntry = new RecursiveString(result, inputParams, saveResult, "UFFun");
    newEntry.setUFName(funcType.getName());
    newEntry.setUFInputType(checkUFInputType(funcType.getArgumentTypes()));
    newEntry.setUFOutputType(checkUFOutputType(funcType.getType()));
    Generator.executedAggregator.add(newEntry);
  }


}
