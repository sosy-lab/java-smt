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

import static org.sosy_lab.java_smt.solvers.SolverLess.SolverLessFormulaCreator.extractBitvectorLengthFromString;
import static org.sosy_lab.java_smt.solvers.SolverLess.SolverLessFormulaCreator.extractExponentFromString;
import static org.sosy_lab.java_smt.solvers.SolverLess.SolverLessFormulaCreator.extractMantissaFromString;


import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.solvers.SolverLess.DummyType.Type;

public class DummyFormula implements Formula, BitvectorFormula, FloatingPointFormula,
                                     ArrayFormula,
                                     NumeralFormula, BooleanFormula,
                                     IntegerFormula
    , RationalFormula {
  private String name ="unnamed";
  private DummyFormula firstArrayParameter = null;
  private DummyFormula secondArrayParameter = null;
  private String representation = "";
  private final DummyType formulaType;
  private String value = "";



  public DummyFormula(DummyType pFormulaType) {
    if(pFormulaType.isArray()){
      DummyFormula formula = createDummyFormulaArrayFromString(pFormulaType.toString());
        firstArrayParameter = formula.getFirstArrayParameter();
        secondArrayParameter = formula.getSecondArrayParameter();
        representation = formula.representation;
        formulaType = formula.formulaType;
        value = formula.value;
        name = formula.name;
    }else{
      formulaType = pFormulaType;
    }
    updateRepresentation();
  }


  public DummyFormula(boolean value) {
    formulaType = new DummyType(Type.BOOLEAN);
    this.value = String.valueOf(value);
    updateRepresentation();
  }


  public DummyFormula(DummyType pFormulaType, String pRepresentation) {
    formulaType = pFormulaType;
    representation = pRepresentation;
    if (pFormulaType.isInteger() || pFormulaType.isRational()) {
      value = pRepresentation;
    }
    updateRepresentation();
  }


  public DummyFormula(
      DummyFormula pFirstArrayParameter,
      DummyFormula pSecondArrayParameter) { //if it represents an array
    representation = "";
    formulaType = new DummyType(pFirstArrayParameter.getFormulaType().myType, pSecondArrayParameter.getFormulaType().myType);
    firstArrayParameter = pFirstArrayParameter;
    secondArrayParameter = pSecondArrayParameter;
    updateRepresentation();
  }

  public DummyFormula(int exponent, int mantissa) { //if it represents a FloatingPoint
    formulaType = new DummyType(exponent, mantissa);
    updateRepresentation();
  }

  public DummyFormula(int pBitvectorLength) {
    formulaType = new DummyType(pBitvectorLength);
    updateRepresentation();
  }
  public void setName(String name){
    this.name = name;
  }
  public String getName(){
    return name;
  }

  /**
   * Helper method which transforms any FormulaType Object into the matching DummyFormula
   * @param pType FormulaType-Object
   * @return DummyFormula with the correct Type.
   */
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
      return new DummyFormula(new DummyType(Type.BOOLEAN));
    } else if (pType.isFloatingPointType()) {
      FormulaType.FloatingPointType floatingPointType = (FormulaType.FloatingPointType) pType;
      int exponentSize = floatingPointType.getExponentSize();
      int mantissaSize = floatingPointType.getMantissaSize();
      return new DummyFormula(exponentSize, mantissaSize);
    } else if (pType.isNumeralType()) {
      if (pType.isIntegerType()) {
        return new DummyFormula(new DummyType(Type.INTEGER));
      } else if (pType.isRationalType()) {
        return new DummyFormula(new DummyType(Type.RATIONAL));
      }
    } else if (pType.isStringType()) {
      return new DummyFormula(new DummyType(Type.STRING));
    } else if (pType.isRegexType()) {
      return new DummyFormula(new DummyType(Type.REGEX));
    } else {
      throw new IllegalArgumentException("Unsupported FormulaType: " + pType);
    }
    throw new RuntimeException("Unsupported FormulaType: " + pType);
  }

  /**
   * This method is an internal helper method which creates the internal representation of
   * an ArrayFormula to be later extracted by the FormulaCreator
   * @return The correct representation as a String
   */
  private String getArrayRepresentation() {
    StringBuilder representationBuilder = new StringBuilder("Array<");

    if (firstArrayParameter.getFormulaType().isArray()) {
      representationBuilder.append(firstArrayParameter.getArrayRepresentation());
    } else {
      representationBuilder.append(firstArrayParameter.getFormulaType());
    }

    representationBuilder.append(", ");

    if (secondArrayParameter.getFormulaType().isArray()) {
      representationBuilder.append(secondArrayParameter.getArrayRepresentation());
    } else {
      representationBuilder.append(secondArrayParameter.getFormulaType());
    }

    representationBuilder.append(">");
    return representationBuilder.toString();
  }

  /**
   * This is the reverse Method to be used in the FormulaCreator. It extracts the indexElement
   * and the Element types from the string to create a matching ArrayFormula
   * @param input String in the Array<IndexElement, Element>
   * @return DummyFormula representing the Array without values.
   */
  public static DummyFormula createDummyFormulaArrayFromString(String input) {
    input = input.trim();

    if (input.startsWith("Array<") && input.endsWith(">")) {

      String content = input.substring(6, input.length() - 1).trim();
      int commaIndex = findTopLevelCommaIndex(content);
      if (commaIndex == -1) {
        throw new IllegalArgumentException("Invalid Array representation: " + input);
      }

      String firstParameter = content.substring(0, commaIndex).trim();
      String secondParameter = content.substring(commaIndex + 1).trim();

      DummyFormula firstArrayParameter = createDummyFormulaArrayFromString(firstParameter);
      DummyFormula secondArrayParameter = createDummyFormulaArrayFromString(secondParameter);


      return new DummyFormula(firstArrayParameter, secondArrayParameter);
    }


    try {
      String convertedType = input.toUpperCase();
      switch (convertedType.substring(0,3)) {
        case "INT":
          return new DummyFormula(new DummyType(Type.INTEGER));
        case "RAT":
          return new DummyFormula(new DummyType(Type.RATIONAL));
        case "BOO":
          return new DummyFormula(new DummyType(Type.BOOLEAN));
        case "STR":
          return new DummyFormula(new DummyType(Type.STRING));
        case "REG":
          return new DummyFormula(new DummyType(Type.REGEX));
        case "BIT":
          return new DummyFormula(new DummyType(extractBitvectorLengthFromString(input)));
        case "FLO":
          return new DummyFormula(new DummyType(extractExponentFromString(input),
              extractMantissaFromString(input)));
        default:
          throw new IllegalArgumentException("Unsupported type: " + input);
      }
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException(
          "Invalid representation or unsupported type: " + input, e);
    }
  }

  /**
   * Internal helper Method which is needed to determine at which index the "," is in order
   * to correctly extract the index and the element types
   * @param content String in the internal array representation
   * @return index of the "," otherwise -1
   */
  private static int findTopLevelCommaIndex(String content) {
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

  /**
   * This method ensures that the DummyFormula has the format which the FormulaCreator needs
   * to extract the information and create a matching DummyFormula from the representation-string
   * This is necessary as the Bitvector, FloatingPoint and Array FormulaTypes need more information
   * as just the FormulaType.
   * The Values are represented too.
   */
  private void updateRepresentation() {
    switch (formulaType.myType) {
      case BITVECTOR:
        this.representation = "Bitvector<" + getBitvectorLength() + ">";
        break;
      case FLOATING_POINT:
        this.representation = "FloatingPoint<" + getExponent() + ", " + getMantissa() + ">";
        break;
      case ARRAY:
        this.representation = getArrayRepresentation();
        break;
      case BOOLEAN:
        this.representation = "Boolean<" + value + ">";
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
        this.representation = formulaType.toString();
        break;
    }
  }


  public DummyType getFormulaType() {
    return formulaType;
  }

  /**
   * This method transforms this DummyFormula into the matching FormulaType Object
   * @return matching Formula Type Object.
   */
  public FormulaType<?> getFormulaTypeForCreator() {
    switch (formulaType.myType) {
      case BITVECTOR:
        return FormulaType.getBitvectorTypeWithSize(getBitvectorLength());
      case FLOATING_POINT:
        return FormulaType.getFloatingPointType(getExponent(), getMantissa());
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
    return formulaType.getExponent();
  }


  public int getMantissa() {
    return formulaType.getMantissa();
  }


  public int getBitvectorLength() {
    return formulaType.getBitvectorLength();
  }


  public DummyFormula getFirstArrayParameter() {
    return firstArrayParameter;
  }


  public DummyFormula getSecondArrayParameter() {
    return secondArrayParameter;
  }


  public String getValue() {
    return value;
  }

  public void setValue(String pValue) {
    value = pValue;
    updateRepresentation();
  }

  @Override
  public String toString() {
    return representation;
  }

  public void setRepresentation(String pS) {
    representation = pS;
  }
}

