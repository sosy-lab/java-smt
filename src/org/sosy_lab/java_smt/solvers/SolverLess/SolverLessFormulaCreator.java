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

import static com.google.common.base.Preconditions.checkArgument;

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

@SuppressWarnings("StringSplitter")
public class SolverLessFormulaCreator
    extends FormulaCreator<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  private final Map<String, DummyFunction> uninterpretedFunctions = new HashMap<>();

  protected SolverLessFormulaCreator() {
    super(
        new DummyEnv(),
        new DummyType(DummyType.Type.BOOLEAN),
        new DummyType(DummyType.Type.INTEGER),
        new DummyType(DummyType.Type.RATIONAL),
        new DummyType(DummyType.Type.STRING),
        new DummyType(DummyType.Type.REGEX));
  }

  @Override
  public DummyType getBitvectorType(int bitwidth) {
    return new DummyType(bitwidth);
  }

  @Override
  public DummyType getFloatingPointType(FloatingPointType type) {
    return new DummyType(type.getExponentSize(), type.getMantissaSize());
  }

  @Override
  public DummyType getArrayType(DummyType indexType, DummyType elementType) {
    return new DummyType(indexType.myType, elementType.myType);
  }

  @Override
  public DummyFormula makeVariable(DummyType pDummyType, String varName) {
    DummyFormula result = new DummyFormula(pDummyType);
    result.setName(varName);
    return result;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    if (formula instanceof DummyFormula) {
      DummyFormula dummyFormula = (DummyFormula) formula;
      switch (dummyFormula.getFormulaType().myType) {
        case BITVECTOR:
          return (FormulaType<T>)
              FormulaType.getBitvectorTypeWithSize(dummyFormula.getBitvectorLength());
        case FLOATING_POINT:
          return (FormulaType<T>)
              FormulaType.getFloatingPointType(
                  dummyFormula.getExponent(), dummyFormula.getMantissa());
        case ARRAY:
          return (FormulaType<T>)
              FormulaType.getArrayType(
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
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(extractInfo(formula).getBitvectorLength());
    }
    if (formula instanceof ArrayFormula) {
      return (FormulaType<T>)
          FormulaType.getArrayType(
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
      return new DummyFormula(
          extractExponentFromString(pT.toString()), extractMantissaFromString(pT.toString()));
    }
    if (pT instanceof RationalFormula) {
      if (pT.toString().isEmpty()) {
        return new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
      }
      DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.RATIONAL), pT.toString());
      return result;
    }
    if (pT instanceof IntegerFormula) {
      if (pT.toString().isEmpty()) {
        return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
      }
      DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.INTEGER), pT.toString());
      return result;
    }
    if (pT instanceof BooleanFormula) {
      if (pT.toString().isEmpty()) {
        return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
      }
      DummyFormula result = new DummyFormula(Boolean.parseBoolean(pT.toString()));
      return result;
    }
    if (pT instanceof ArrayFormula) {
      DummyFormula.createDummyFormulaArrayFromString(pT.toString());
    }

    return super.extractInfo(pT);
  }

  public static int extractBitvectorLengthFromString(String representation) {
    if (representation.startsWith("Bitvector<") && representation.endsWith(">")) {
      try {
        String lengthStr = representation.substring(10, representation.length() - 1);
        return Integer.parseInt(lengthStr);
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException(
            "Invalid Bitvector representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid Bitvector representation: " + representation);
  }

  public static int extractExponentFromString(String representation) {
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
    } else if (representation.startsWith("(fp #b")) {
      try {
        String[] parts = representation.split(" ");
        if (parts.length != 4) {
          throw new IllegalArgumentException(
              "Invalid FloatingPoint representation: " + representation);
        }
        return parts[2].length() - 2; // Remove #b prefix and count bits
      } catch (Exception e) {
        throw new IllegalArgumentException(
            "Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }

  public static int extractMantissaFromString(String representation) {
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
    } else if (representation.startsWith("(fp #b")) {
      try {
        String[] parts = representation.split(" ");
        if (parts.length != 4) {
          throw new IllegalArgumentException(
              "Invalid FloatingPoint representation: " + representation);
        }
        return parts[3].length() - 2; // Remove #b prefix and count bits
      } catch (Exception e) {
        throw new IllegalArgumentException(
            "Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }

  @Override
  public DummyFunction declareUFImpl(
      String pName, DummyType pReturnType, List<DummyType> pArgTypes) {
    checkArgument(!pName.isEmpty(), "UF name cannot be null or empty");

    return uninterpretedFunctions.computeIfAbsent(
        pName,
        key -> {
          DummyFunction function = new DummyFunction();
          function.setName(key);
          function.setReturnType(pReturnType);
          function.setArgumentTypes(pArgTypes);
          return function;
        });
  }

  @Override
  public DummyFormula callFunctionImpl(DummyFunction declaration, List<DummyFormula> args) {
    checkArgument(!args.contains(null), "Arguments cannot be null");
    List<DummyType> expectedTypes = declaration.getArgumentTypes();
    if (args.size() != expectedTypes.size()) {
      throw new IllegalArgumentException(
          String.format("Expected %d arguments, but got %d", expectedTypes.size(), args.size()));
    }
    for (int i = 0; i < args.size(); i++) {
      DummyType expected = expectedTypes.get(i);
      DummyType actual = args.get(i).getFormulaType();
      if (!expected.equals(actual)) {
        throw new IllegalArgumentException(
            String.format("Argument %d has type %s, but expected %s", i, actual, expected));
      }
    }
    DummyFormula result;
    if (declaration.getReturnType().isBitvector()) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().isBitvector()) {
          result = new DummyFormula(arg.getBitvectorLength());
        }
      }
    }
    if (declaration.getReturnType().isFloatingPoint()) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().isFloatingPoint()) {
          result = new DummyFormula(arg.getExponent(), arg.getMantissa());
        }
      }
    }
    if (declaration.getReturnType().isArray()) {
      for (DummyFormula arg : args) {
        if (arg.getFormulaType().isArray()) {
          result = new DummyFormula(arg.getFirstArrayParameter(), arg.getSecondArrayParameter());
        }
      }
    }
    result = new DummyFormula(declaration.getReturnType());
    result.setName(declaration.getName());

    return result;
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(DummyFormula pDummyFormula) {
    return new DummyFunction(); // not supported
  }
}
