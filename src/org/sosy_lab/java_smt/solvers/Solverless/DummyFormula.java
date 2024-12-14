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

import java.text.Normalizer.Form;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class DummyFormula implements Formula, BitvectorFormula, FloatingPointFormula,
                                     ArrayFormula, NumeralFormula, BooleanFormula, IntegerFormula
                                         , RationalFormula {
  private String name;
  private  int exponent = -1;
  private  int mantissa = -1;
  private  int bitvectorLength = -1;
  private  DummyFormula firstArrayParameter = null;
  private  DummyFormula secondArrayParameter = null;
  private  String representation ="";
  private final FormulaTypesForChecking formulaType;
  private  String value ="";


  public DummyFormula(FormulaTypesForChecking pFormulaType) {
    formulaType = pFormulaType;
    updateRepresentation();
  }


  public DummyFormula(FormulaTypesForChecking pFormulaType, String pRepresentation) {
    formulaType = pFormulaType;
    representation = pRepresentation;
    if(pFormulaType == FormulaTypesForChecking.RATIONAL|| pFormulaType == FormulaTypesForChecking.INTEGER) {
      value = pRepresentation;
    }
    updateRepresentation();
  }


  public String getName() {
    return name;
  }

  public void setName(String pName) {
    name = pName;
  }

  public DummyFormula(DummyFormula pfirstArrayParameter,
                      DummyFormula psecondArrayParameter) { //if it represents an array
    representation = "";
    formulaType = FormulaTypesForChecking.ARRAY;
    firstArrayParameter = pfirstArrayParameter;
    secondArrayParameter = psecondArrayParameter;
    updateRepresentation();
  }
  public DummyFormula (int exponent, int mantissa){ //if it represents a FloatingPoint
    this.exponent = exponent;
    this.mantissa = mantissa;
    formulaType = FormulaTypesForChecking.FLOATING_POINT;
    updateRepresentation();
  }
  public DummyFormula (int pBitvectorLength){
    this.bitvectorLength = pBitvectorLength;
    formulaType = FormulaTypesForChecking.BITVECTOR;
    updateRepresentation();
  }

  public static DummyFormula getDummyFormulaFromObject(FormulaType<?> pType) {
    if (pType.isArrayType()) {
      FormulaType.ArrayFormulaType<?, ?> arrayType = (FormulaType.ArrayFormulaType<?, ?>) pType;
      FormulaType<?> indexType = arrayType.getIndexType();
      FormulaType<?> elementType = arrayType.getElementType();
      return new DummyFormula(getDummyFormulaFromObject(indexType),
          getDummyFormulaFromObject(elementType));
    } else if (pType.isBitvectorType()) {
      FormulaType.BitvectorType bitvectorType = (FormulaType.BitvectorType) pType;
      int size = bitvectorType.getSize();
      return new DummyFormula(size);
    } else if (pType.isBooleanType()) {
      return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
    } else if (pType.isFloatingPointType()) {
      FormulaType.FloatingPointType floatingPointType = (FormulaType.FloatingPointType) pType;
      int exponentSize = floatingPointType.getExponentSize();
      int mantissaSize = floatingPointType.getMantissaSize();
      return new DummyFormula(exponentSize, mantissaSize);
    } else if (pType.isNumeralType()) {
      if (pType.isIntegerType()) {
        return new DummyFormula(FormulaTypesForChecking.INTEGER);
      } else if (pType.isRationalType()) {
        return new DummyFormula(FormulaTypesForChecking.RATIONAL);
      }
    } else if (pType.isStringType()) {
      return new DummyFormula(FormulaTypesForChecking.STRING);
    } else if (pType.isRegexType()) {
      return new DummyFormula(FormulaTypesForChecking.REGEX);
    } else {
      throw new IllegalArgumentException("Unsupported FormulaType: " + pType);
    }
    return null;
  }

  private void updateRepresentation() {
    switch (formulaType) {
      case BITVECTOR:
        this.representation = "Bitvector<" + bitvectorLength + ">";
        break;
      case FLOATING_POINT:
        this.representation = "FloatingPoint<" + exponent + ", " + mantissa + ">";
        break;
      case ARRAY:
        this.representation = "Array<" + firstArrayParameter + ", " + secondArrayParameter + ">";
        break;
      case BOOLEAN:
        this.representation = "Boolean";
        break;
      case INTEGER:
      case RATIONAL:
        this.representation = value;
        break;
      case STRING:
        this.representation = "String";
        break;
      case REGEX:
        this.representation = "Regex";
        break;
      default:
        this.representation = "Unknown";
        break;
    }
  }

  public FormulaTypesForChecking getFormulaType() {
    return formulaType;
  }

  public FormulaType<?> getFormulaTypeForCreator(){
    switch(formulaType){
      case BITVECTOR:
        return FormulaType.getBitvectorTypeWithSize(bitvectorLength);
      case FLOATING_POINT:
        return FormulaType.getFloatingPointType(exponent, mantissa);
      case ARRAY:
        return FormulaType.getArrayType(firstArrayParameter.getFormulaTypeForCreator(),
            secondArrayParameter.getFormulaTypeForCreator());
      case RATIONAL:
        return FormulaType.RationalType;
      case STRING:
        return FormulaType.StringType;
      case REGEX:
        return FormulaType.RegexType;
      case INTEGER:
        return FormulaType.IntegerType;
      default:
        return FormulaType.BooleanType;
    }
  }

  public int getExponent() {
    return exponent;
  }

  public void setExponent(int pExponent) {
    exponent = pExponent;
  }

  public int getMantissa() {
    return mantissa;
  }

  public void setMantissa(int pMantissa) {
    mantissa = pMantissa;
  }

  public int getBitvectorLength() {
    return bitvectorLength;
  }

  public void setBitvectorLength(int pBitvectorLength) {
    bitvectorLength = pBitvectorLength;
  }

  public DummyFormula getFirstArrayParameter() {
    return firstArrayParameter;
  }

  public void setFirstArrayParameter(DummyFormula pFirstArrayParameter) {
    firstArrayParameter = pFirstArrayParameter;
  }

  public DummyFormula getSecondArrayParameter() {
    return secondArrayParameter;
  }

  public void setSecondArrayParameter(DummyFormula pSecondArrayParameter) {
    secondArrayParameter = pSecondArrayParameter;
  }

  @Override
  public String toString() {
    return representation;
  }

  public void setRepresentation(String pS) {
    representation = pS;
  }
}

