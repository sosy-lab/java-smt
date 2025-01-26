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

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessFormulaCreator
    extends FormulaCreator<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> {

  private final Map<String, DummyFunction> uninterpretedFunctions = new HashMap<>();

  protected SolverLessFormulaCreator() {
    super(new DummyEnv(), FormulaTypesForChecking.BOOLEAN, FormulaTypesForChecking.INTEGER,
        FormulaTypesForChecking.RATIONAL,
        FormulaTypesForChecking.STRING,
        FormulaTypesForChecking.REGEX);
  }

  @Override
  public FormulaTypesForChecking getBitvectorType(int bitwidth) {
    return FormulaTypesForChecking.BITVECTOR;
  }

  @Override
  public FormulaTypesForChecking getFloatingPointType(FloatingPointType type) {
    return FormulaTypesForChecking.FLOATING_POINT;
  }

  @Override
  public FormulaTypesForChecking getArrayType(
      FormulaTypesForChecking indexType,
      FormulaTypesForChecking elementType) {
    return FormulaTypesForChecking.ARRAY;
  }

  @Override
  public DummyFormula makeVariable(
      FormulaTypesForChecking pFormulaTypesForChecking,
      String varName) {
    DummyFormula result = new DummyFormula(pFormulaTypesForChecking);
    result.setName(varName);
    return result;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    if (formula instanceof DummyFormula) {
      DummyFormula dummyFormula = (DummyFormula) formula;
      switch (dummyFormula.getFormulaType()) {
        case BITVECTOR:
          return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(
              dummyFormula.getBitvectorLength());
        case FLOATING_POINT:
          return (FormulaType<T>) FormulaType.getFloatingPointType(dummyFormula.getExponent(),
              dummyFormula.getMantissa());
        case ARRAY:
          return (FormulaType<T>) FormulaType.getArrayType(
              dummyFormula.getFirstArrayParameter().getFormulaTypeForCreator(),
              dummyFormula.getSecondArrayParameter().getFormulaTypeForCreator());
        case RATIONAL:
          return (FormulaType<T>) FormulaType.RationalType;
        case STRING:
          return (FormulaType<T>) FormulaType.StringType;
        case REGEX:
          return (FormulaType<T>) FormulaType.RegexType;
        case INTEGER:
          return (FormulaType<T>) FormulaType.IntegerType;
        default:
          return (FormulaType<T>) FormulaType.BooleanType;
      }
    }
    if (formula instanceof BitvectorFormula) {
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(
          extractInfo(formula).getBitvectorLength());
    }
    if (formula instanceof ArrayFormula) {
      return (FormulaType<T>) FormulaType.getArrayType(
          extractInfo(formula).getFirstArrayParameter().getFormulaTypeForCreator(),
          extractInfo(formula).getSecondArrayParameter().getFormulaTypeForCreator());
    }
    return super.getFormulaType(formula);
  }

  @Override
  public FormulaType<?> getFormulaType(DummyFormula formula) {
    return formula.getFormulaTypeForCreator();
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DummyFormula f) {
    return null;
  }

  @Override
  protected DummyFormula extractInfo(Formula pT) {
    if (pT instanceof DummyFormula) {
      return (DummyFormula) pT;
    }
    if (pT instanceof BitvectorFormula) {
      return new DummyFormula(extractBitvectorLengthFromString(pT.toString()));
    }
    if (pT instanceof FloatingPointFormula) {
      return new DummyFormula(extractExponentFromString(pT.toString()),
          extractMantissaFromString(pT.toString()));
    }
    if (pT instanceof RationalFormula) {
      if (pT.toString().equals("")) {
        return new DummyFormula(FormulaTypesForChecking.RATIONAL);
      }
      DummyFormula result = new DummyFormula(FormulaTypesForChecking.RATIONAL,
          (pT.toString()));
      return result;
    }
    if (pT instanceof IntegerFormula) {
      if (pT.toString().equals("")) {
        return new DummyFormula(FormulaTypesForChecking.INTEGER);
      }
      DummyFormula result = new DummyFormula(FormulaTypesForChecking.INTEGER,
          pT.toString());
      return result;
    }
    if (pT instanceof BooleanFormula) {
      if (pT.toString().equals("")) {
        return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
      }
      DummyFormula result = new DummyFormula(Boolean.parseBoolean(pT.toString()));
      return result;
    }
    if (pT instanceof ArrayFormula) {
      if (pT.toString().equals("") || pT.toString().equals("Array<, >")) {
        return new DummyFormula(FormulaTypesForChecking.ARRAY);
      }
      DummyFormula.createDummyFormulaArrayFromString(pT.toString());
    }

    return super.extractInfo(pT);
  }

  public String extractFirstArrayParameterFromString(String representation) {
    if (representation.startsWith("Array<") && representation.endsWith(">")) {
      try {

        String content = representation.substring(6, representation.length() - 1).trim();


        int commaIndex = findTopLevelCommaIndex(content);
        if (commaIndex == -1) {
          throw new IllegalArgumentException("Invalid Array representation: " + representation);
        }


        return content.substring(0, commaIndex).trim();
      } catch (StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid Array representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid Array representation: " + representation);
  }

  private int findTopLevelCommaIndex(String content) {
    int depth = 0;
    for (int i = 0; i < content.length(); i++) {
      char c = content.charAt(i);
      if (c == '<') {
        depth++;
      } else if (c == '>') {
        depth--;
      } else if (c == ',' && depth == 0) {
        return i;
      }
    }
    return -1;
  }

  public String extractSecondArrayParameterFromString(String representation) {
    if (representation.startsWith("Array<") && representation.endsWith(">")) {
      try {

        String content = representation.substring(6, representation.length() - 1).trim();

        int commaIndex = findTopLevelCommaIndex(content);
        if (commaIndex == -1) {
          throw new IllegalArgumentException("Invalid Array representation: " + representation);
        }

        return content.substring(commaIndex + 1).trim();
      } catch (StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid Array representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid Array representation: " + representation);
  }


  public int extractBitvectorLengthFromString(String representation) {
    if (representation.startsWith("Bitvector<") && representation.endsWith(">")) {
      try {
        String lengthStr = representation.substring(10, representation.length() - 1);
        return Integer.parseInt(lengthStr);
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid Bitvector representation: " + representation,
            e);
      }
    }
    throw new IllegalArgumentException("Invalid Bitvector representation: " + representation);
  }

  public int extractExponentFromString(String representation) {
    if (representation.startsWith("FloatingPoint<") && representation.endsWith(">")) {
      try {
        String[] parts = representation.substring(14, representation.length() - 1).split(",");
        if (parts.length != 2) {
          throw new IllegalArgumentException(
              "Invalid FloatingPoint representation: " + representation);
        }
        return Integer.parseInt(parts[0].trim());
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException(
            "Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }

  public int extractMantissaFromString(String representation) {
    if (representation.startsWith("FloatingPoint<") && representation.endsWith(">")) {
      try {
        String[] parts = representation.substring(14, representation.length() - 1).split(",");
        if (parts.length != 2) {
          throw new IllegalArgumentException(
              "Invalid FloatingPoint representation: " + representation);
        }
        return Integer.parseInt(parts[1].trim());
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException(
            "Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }


  @Override
  public DummyFunction declareUFImpl(
      String pName,
      FormulaTypesForChecking pReturnType,
      List<FormulaTypesForChecking> pArgTypes) {
    if (pName.isEmpty()) {
      throw new IllegalArgumentException("UF name cannot be null or empty");
    }

    return uninterpretedFunctions.computeIfAbsent(pName, key -> {
      DummyFunction function = new DummyFunction();
      function.setName(key);
      function.setReturnType(pReturnType);
      function.setArgumentTypes(pArgTypes);
      return function;
    });
  }

  @Override
  public DummyFormula callFunctionImpl(DummyFunction declaration, List<DummyFormula> args) {
    if (args.contains(null)) {
      throw new IllegalArgumentException("Arguments cannot be null");
    }

    List<FormulaTypesForChecking> expectedTypes = declaration.getArgumentTypes();
    if (args.size() != expectedTypes.size()) {
      throw new IllegalArgumentException(
          String.format("Expected %d arguments, but got %d", expectedTypes.size(), args.size()));
    }
    for (int i = 0; i < args.size(); i++) {
      FormulaTypesForChecking expected = expectedTypes.get(i);
      FormulaTypesForChecking actual = args.get(i).getFormulaType();
      if (!expected.equals(actual)) {
        throw new IllegalArgumentException(
            String.format("Argument %d has type %s, but expected %s", i, actual, expected));
      }
    }
    DummyFormula result;
    if (declaration.getReturnType().equals(FormulaTypesForChecking.BITVECTOR)) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().equals(FormulaTypesForChecking.BITVECTOR)) {
          result = new DummyFormula(arg.getBitvectorLength());
        }
      }
    }
    if (declaration.getReturnType().equals(FormulaTypesForChecking.FLOATING_POINT)) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().equals(FormulaTypesForChecking.FLOATING_POINT)) {
          result = new DummyFormula(arg.getExponent(), arg.getMantissa());
        }
      }
    }
    if (declaration.getReturnType().equals(FormulaTypesForChecking.ARRAY)) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().equals(FormulaTypesForChecking.ARRAY)) {
          result = new DummyFormula(arg.getFirstArrayParameter(),
              arg.getSecondArrayParameter());
        }
      }
    }
    result = new DummyFormula(declaration.getReturnType());
    result.setName(declaration.getName());
    /*
    result.setRepresentation(declaration.getName() + "(" +
        args.stream().map(DummyFormula::toString).reduce((arg1, arg2) -> arg1 + ", " + arg2).orElse("") +
        ")");
     */

    return result;
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(DummyFormula pDummyFormula) {
    return new DummyFunction();
  }
}
