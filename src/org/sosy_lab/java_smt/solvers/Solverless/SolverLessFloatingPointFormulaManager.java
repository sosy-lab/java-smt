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

import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessFloatingPointFormulaManager extends
                                                   AbstractFloatingPointFormulaManager<String, String, String, String> {

  protected SolverLessFloatingPointFormulaManager(FormulaCreator<String, String, String, String> pCreator) {
    super(pCreator);
  }

  @Override
  protected String getDefaultRoundingMode() {
    return "";
  }

  @Override
  protected String getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String makeNumberImpl(
      double n,
      FloatingPointType type,
      String pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String makeNumberAndRound(
      String pN,
      FloatingPointType pType,
      String pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String makeVariableImpl(String pVar, FloatingPointType pType) {
    return "";
  }

  @Override
  protected String makePlusInfinityImpl(FloatingPointType pType) {
    return "";
  }

  @Override
  protected String makeMinusInfinityImpl(FloatingPointType pType) {
    return "";
  }

  @Override
  protected String makeNaNImpl(FloatingPointType pType) {
    return "";
  }

  @Override
  protected String castToImpl(
      String pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      String pRoundingMode) {
    return "";
  }

  @Override
  protected String castFromImpl(
      String pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      String pRoundingMode) {
    return "";
  }

  @Override
  protected String fromIeeeBitvectorImpl(String pNumber, FloatingPointType pTargetType) {
    return "";
  }

  @Override
  protected String toIeeeBitvectorImpl(String pNumber) {
    return "";
  }

  @Override
  protected String negate(String pParam1) {
    return "";
  }

  @Override
  protected String abs(String pParam1) {
    return "";
  }

  @Override
  protected String max(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String min(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String sqrt(String pNumber, String pRoundingMode) {
    return "";
  }

  @Override
  protected String add(String pParam1, String pParam2, String pRoundingMode) {
    return "";
  }

  @Override
  protected String subtract(String pParam1, String pParam2, String pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String divide(String pParam1, String pParam2, String pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String multiply(String pParam1, String pParam2, String pFloatingPointRoundingMode) {
    return "";
  }

  @Override
  protected String assignment(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String equalWithFPSemantics(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String greaterThan(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String greaterOrEquals(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String lessThan(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String lessOrEquals(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String isNaN(String pParam) {
    return "";
  }

  @Override
  protected String isInfinity(String pParam) {
    return "";
  }

  @Override
  protected String isZero(String pParam) {
    return "";
  }

  @Override
  protected String isSubnormal(String pParam) {
    return "";
  }

  @Override
  protected String isNormal(String pParam) {
    return "";
  }

  @Override
  protected String isNegative(String pParam) {
    return "";
  }

  @Override
  protected String round(String pFormula, FloatingPointRoundingMode pRoundingMode) {
    return "";
  }
}
