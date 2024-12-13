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

import com.sun.jdi.IntegerType;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessFloatingPointFormulaManager extends
                                                   AbstractFloatingPointFormulaManager<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> {

  protected SolverLessFloatingPointFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  protected DummyFormula getDefaultRoundingMode() {
    return new DummyFormula("", FormulaTypesForChecking.FLOATING_POINT);
  }

  @Override
  protected DummyFormula getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return new DummyFormula("", FormulaTypesForChecking.FLOATING_POINT);
  }

  @Override
  protected DummyFormula makeNumberImpl(
      double n,
      FloatingPointType type,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(type.getExponentSize(), type.getMantissaSize());
  }

  @Override
  protected DummyFormula makeNumberAndRound(
      String pN,
      FloatingPointType pType,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected DummyFormula makeVariableImpl(String pVar, FloatingPointType pType) {
    DummyFormula formula = new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setName(pVar);
    return formula;
  }

  @Override
  protected DummyFormula makePlusInfinityImpl(FloatingPointType pType) {
    return new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected DummyFormula makeMinusInfinityImpl(FloatingPointType pType) {
    return new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected DummyFormula makeNaNImpl(FloatingPointType pType) {
    return new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected DummyFormula castToImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      DummyFormula pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      return new DummyFormula(targetType.getExponentSize(), targetType.getMantissaSize());
    }
    if (pTargetType.isIntegerType()) {
      return new DummyFormula("", FormulaTypesForChecking.INTEGER);
    }
    if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      return new DummyFormula(targetType.getSize());
    }
    if (pTargetType.isRationalType()) {
      return new DummyFormula("", FormulaTypesForChecking.RATIONAL);
    }
    return null;
  }

  @Override
  protected DummyFormula castFromImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      DummyFormula pRoundingMode) {
    return new DummyFormula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected DummyFormula fromIeeeBitvectorImpl(
      DummyFormula pNumber,
      FloatingPointType pTargetType) {
    return new DummyFormula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected DummyFormula toIeeeBitvectorImpl(DummyFormula pNumber) {
    return new DummyFormula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula abs(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula max(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula min(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula sqrt(DummyFormula pNumber, DummyFormula pRoundingMode) {
    return new DummyFormula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected DummyFormula add(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula subtract(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula divide(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula multiply(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula assignment(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula equalWithFPSemantics(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isNaN(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isInfinity(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isZero(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isSubnormal(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isNormal(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula isNegative(DummyFormula pParam) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula round(DummyFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return new DummyFormula(pFormula.getExponent(), pFormula.getMantissa());
  }
}


