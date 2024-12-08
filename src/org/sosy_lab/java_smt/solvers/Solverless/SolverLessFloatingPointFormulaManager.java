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
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessFloatingPointFormulaManager extends
                                                    AbstractFloatingPointFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFloatingPointFormulaManager() {
    super(new SolverLessFormulaCreator());
  }
  @Override
  protected DummyFormula getDefaultRoundingMode() {
    return null;
  }

  @Override
  protected DummyFormula getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula makeNumberImpl(
      double n,
      FloatingPointType type,
      DummyFormula pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula makeNumberAndRound(
      String pN,
      FloatingPointType pType,
      DummyFormula pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula makeVariableImpl(String pVar, FloatingPointType pType) {
    return null;
  }

  @Override
  protected DummyFormula makePlusInfinityImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected DummyFormula makeMinusInfinityImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected DummyFormula makeNaNImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected DummyFormula castToImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      DummyFormula pRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula castFromImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      DummyFormula pRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula fromIeeeBitvectorImpl(
      DummyFormula pNumber,
      FloatingPointType pTargetType) {
    return null;
  }

  @Override
  protected DummyFormula toIeeeBitvectorImpl(DummyFormula pNumber) {
    return null;
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return null;
  }

  @Override
  protected DummyFormula abs(DummyFormula pParam1) {
    return null;
  }

  @Override
  protected DummyFormula max(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula min(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula sqrt(DummyFormula pNumber, DummyFormula pRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula add(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula subtract(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula divide(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula multiply(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected DummyFormula assignment(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula equalWithFPSemantics(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return null;
  }

  @Override
  protected DummyFormula isNaN(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula isInfinity(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula isZero(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula isSubnormal(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula isNormal(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula isNegative(DummyFormula pParam) {
    return null;
  }

  @Override
  protected DummyFormula round(DummyFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return null;
  }
}

