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
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class DummyFormula implements Formula {
  private String name;
  private  int exponent = -1;
  private  int mantissa = -1;
  private  int bitvectorLength = -1;
  private  DummyFormula firstArrayParameter = null;
  private  DummyFormula secondArrayParameter = null;

  private  String representation ="";
  private final FormulaTypesForChecking formulaType;


  public DummyFormula(String representation, FormulaTypesForChecking pFormulaType) { //all other
    // sorts
    this.representation = representation;
    formulaType = pFormulaType;
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
  }
  public DummyFormula ( int exponent, int mantissa){ //if it represents a FloatingPoint
    this.exponent = exponent;
    this.mantissa = mantissa;
    formulaType = FormulaTypesForChecking.FLOATING_POINT;
  }
  public DummyFormula ( int pBitvectorLength){
    this.bitvectorLength = pBitvectorLength;
    formulaType = FormulaTypesForChecking.BITVECTOR;
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
}

