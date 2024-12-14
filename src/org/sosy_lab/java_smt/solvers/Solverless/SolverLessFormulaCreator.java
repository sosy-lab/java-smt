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

package org.sosy_lab.java_smt.solvers.Solverless;
import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessFormulaCreator
    extends FormulaCreator<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> {

  protected SolverLessFormulaCreator(){
    super(new DummyEnv(), FormulaTypesForChecking.BOOLEAN , FormulaTypesForChecking.INTEGER, FormulaTypesForChecking.RATIONAL,
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
          return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(dummyFormula.getBitvectorLength());
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
    if(formula instanceof BitvectorFormula) {
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(extractInfo(formula).getBitvectorLength());
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
    if(pT instanceof DummyFormula) {
      return (DummyFormula) pT;
    }
    if(pT instanceof BitvectorFormula){
      return new DummyFormula(extractBitvectorLengthFromString(pT.toString()));
    }
    if(pT instanceof FloatingPointFormula){
      return new DummyFormula(extractExponentFromString(pT.toString()), extractMantissaFromString(pT.toString()));
    }
    return new DummyFormula(FormulaTypesForChecking.DUMMY);
  }
  public int extractBitvectorLengthFromString(String representation) {
    if (representation.startsWith("Bitvector<") && representation.endsWith(">")) {
      try {
        String lengthStr = representation.substring(10, representation.length() - 1);
        return Integer.parseInt(lengthStr);
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid Bitvector representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid Bitvector representation: " + representation);
  }
  public int extractExponentFromString(String representation) {
    if (representation.startsWith("FloatingPoint<") && representation.endsWith(">")) {
      try {
        String[] parts = representation.substring(14, representation.length() - 1).split(",");
        if (parts.length != 2) {
          throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
        }
        return Integer.parseInt(parts[0].trim());
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }

  public int extractMantissaFromString(String representation) {
    if (representation.startsWith("FloatingPoint<") && representation.endsWith(">")) {
      try {
        String[] parts = representation.substring(14, representation.length() - 1).split(",");
        if (parts.length != 2) {
          throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
        }
        return Integer.parseInt(parts[1].trim());
      } catch (NumberFormatException | StringIndexOutOfBoundsException e) {
        throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation, e);
      }
    }
    throw new IllegalArgumentException("Invalid FloatingPoint representation: " + representation);
  }

  @Override
  public DummyFormula callFunctionImpl(DummyFunction declaration, List<DummyFormula> args) {
    return new DummyFormula(args.get(0).getFormulaType());
  }

  @Override
  public DummyFunction declareUFImpl(
      String pName,
      FormulaTypesForChecking pReturnType,
      List<FormulaTypesForChecking> pArgTypes) {
    return new DummyFunction();
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(DummyFormula pDummyFormula) {
    return new DummyFunction();
  }


}
