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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaFloatingPointManager extends
                                          AbstractFloatingPointFormulaManager<Long, Long, Long, Long> {
  protected BitwuzlaFloatingPointManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
  }

  @Override
  protected Long getDefaultRoundingMode() {
    return null;
  }

  @Override
  protected Long getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long makeNumberImpl(double n, FloatingPointType type, Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long makeNumberAndRound(
      String pN,
      FloatingPointType pType,
      Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long makeVariableImpl(String pVar, FloatingPointType pType) {
    return null;
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType pType) {
    return null;
  }

  @Override
  protected Long castToImpl(
      Long pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      Long pRoundingMode) {
    return null;
  }

  @Override
  protected Long castFromImpl(
      Long pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      Long pRoundingMode) {
    return null;
  }

  @Override
  protected Long fromIeeeBitvectorImpl(Long pNumber, FloatingPointType pTargetType) {
    return null;
  }

  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    return null;
  }

  @Override
  protected Long negate(Long pParam1) {
    return null;
  }

  @Override
  protected Long abs(Long pParam1) {
    return null;
  }

  @Override
  protected Long max(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long min(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long sqrt(Long pNumber, Long pRoundingMode) {
    return null;
  }

  @Override
  protected Long add(Long pParam1, Long pParam2, Long pRoundingMode) {
    return null;
  }

  @Override
  protected Long subtract(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long divide(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long multiply(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long assignment(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long equalWithFPSemantics(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long isNaN(Long pParam) {
    return null;
  }

  @Override
  protected Long isInfinity(Long pParam) {
    return null;
  }

  @Override
  protected Long isZero(Long pParam) {
    return null;
  }

  @Override
  protected Long isSubnormal(Long pParam) {
    return null;
  }

  @Override
  protected Long isNormal(Long pParam) {
    return null;
  }

  @Override
  protected Long isNegative(Long pParam) {
    return null;
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    return null;
  }
}
