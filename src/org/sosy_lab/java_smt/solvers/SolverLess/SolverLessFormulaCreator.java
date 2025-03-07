// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;
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
    extends FormulaCreator<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

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
  public SMTLIB2Formula makeVariable(DummyType pDummyType, String varName) {
    SMTLIB2Formula result = new SMTLIB2Formula(pDummyType);
    result.setName(varName);
    return result;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    if (formula instanceof SMTLIB2Formula) {
      SMTLIB2Formula solverLessFormula = (SMTLIB2Formula) formula;
      switch (solverLessFormula.getFormulaType().myType) {
        case BITVECTOR:
          return (FormulaType<T>)
              FormulaType.getBitvectorTypeWithSize(solverLessFormula.getBitvectorLength());
        case FLOATING_POINT:
          return (FormulaType<T>)
              FormulaType.getFloatingPointType(
                  solverLessFormula.getExponent(), solverLessFormula.getMantissa());
        case ARRAY:
          return (FormulaType<T>)
              FormulaType.getArrayType(
                  solverLessFormula.getFirstArrayParameter().getFormulaTypeForCreator(),
                  solverLessFormula.getSecondArrayParameter().getFormulaTypeForCreator());
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
  public FormulaType<?> getFormulaType(SMTLIB2Formula formula) {
    return formula.getFormulaTypeForCreator();
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, SMTLIB2Formula f) {
    return null;
  }

  @Override
  protected SMTLIB2Formula extractInfo(Formula pT) {
    if (pT instanceof SMTLIB2Formula) {
      return (SMTLIB2Formula) pT;
    }
    if (pT instanceof BitvectorFormula) {
      return new SMTLIB2Formula(extractBitvectorLengthFromString(pT.toString()));
    }
    if (pT instanceof FloatingPointFormula) {
      return new SMTLIB2Formula(
          extractExponentFromString(pT.toString()), extractMantissaFromString(pT.toString()));
    }
    if (pT instanceof RationalFormula) {
      if (pT.toString().isEmpty()) {
        return new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL));
      }
      SMTLIB2Formula result =
          new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL), pT.toString());
      return result;
    }
    if (pT instanceof IntegerFormula) {
      if (pT.toString().isEmpty()) {
        return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
      }
      SMTLIB2Formula result =
          new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), pT.toString());
      return result;
    }
    if (pT instanceof BooleanFormula) {
      if (pT.toString().isEmpty()) {
        return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
      }
      SMTLIB2Formula result = new SMTLIB2Formula(Boolean.parseBoolean(pT.toString()));
      return result;
    }
    if (pT instanceof ArrayFormula) {
      SMTLIB2Formula.createDummyFormulaArrayFromString(pT.toString());
    }

    return super.extractInfo(pT);
  }

  @Override
  public void extractVariablesAndUFs(
      final SMTLIB2Formula pFormula,
      final boolean extractUF,
      final BiConsumer<String, SMTLIB2Formula> pConsumer) {
    super.extractVariablesAndUFs(
        (Formula) pFormula, extractUF, (name, f) -> pConsumer.accept(name, (SMTLIB2Formula) f));
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
  public SMTLIB2Formula callFunctionImpl(DummyFunction declaration, List<SMTLIB2Formula> args) {
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
    SMTLIB2Formula result;
    if (declaration.getReturnType().isBitvector()) {
      for (SMTLIB2Formula arg : args) {
        if (arg.getFormulaType().isBitvector()) {
          result = new SMTLIB2Formula(arg.getBitvectorLength());
        }
      }
    }
    if (declaration.getReturnType().isFloatingPoint()) {
      for (SMTLIB2Formula arg : args) {
        if (arg.getFormulaType().isFloatingPoint()) {
          result = new SMTLIB2Formula(arg.getExponent(), arg.getMantissa());
        }
      }
    }
    if (declaration.getReturnType().isArray()) {
      for (SMTLIB2Formula arg : args) {
        if (arg.getFormulaType().isArray()) {
          result = new SMTLIB2Formula(arg.getFirstArrayParameter(), arg.getSecondArrayParameter());
        }
      }
    }
    result = new SMTLIB2Formula(declaration.getReturnType());
    result.setName(declaration.getName());

    return result;
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(SMTLIB2Formula pSMTLIB2Formula) {
    return new DummyFunction(); // not supported
  }
}
