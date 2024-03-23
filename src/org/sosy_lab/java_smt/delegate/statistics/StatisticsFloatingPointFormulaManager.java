// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

class StatisticsFloatingPointFormulaManager implements FloatingPointFormulaManager {

  private final FloatingPointFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsFloatingPointFormulaManager(
      FloatingPointFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public FloatingPointFormula makeNumber(double pN, FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType);
  }

  @Override
  public FloatingPointFormula makeNumber(
      double pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal pN, FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType);
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal pN,
      FloatingPointType pType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String pN, FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType);
  }

  @Override
  public FloatingPointFormula makeNumber(
      String pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(Rational pN, FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType);
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeVariable(pVar, pType);
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makePlusInfinity(pType);
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeMinusInfinity(pType);
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType pType) {
    stats.fpOperations.getAndIncrement();
    return delegate.makeNaN(pType);
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber, boolean pSigned, FormulaType<T> pTargetType) {
    stats.fpOperations.getAndIncrement();
    return delegate.castTo(pNumber, pSigned, pTargetType);
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber,
      boolean pSigned,
      FormulaType<T> pTargetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.castTo(pNumber, pSigned, pTargetType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula pSource, boolean pSigned, FloatingPointType pTargetType) {
    stats.fpOperations.getAndIncrement();
    return delegate.castFrom(pSource, pSigned, pTargetType);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula pSource,
      boolean pSigned,
      FloatingPointType pTargetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.castFrom(pSource, pSigned, pTargetType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula pNumber, FloatingPointType pTargetType) {
    stats.fpOperations.getAndIncrement();
    return delegate.fromIeeeBitvector(pNumber, pTargetType);
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.toIeeeBitvector(pNumber);
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.round(pFormula, pRoundingMode);
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.negate(pNumber);
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.abs(pNumber);
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.max(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.min(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.sqrt(pNumber);
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula pNumber, FloatingPointRoundingMode pRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.sqrt(pNumber, pRoundingMode);
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.add(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.add(pNumber1, pNumber2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.subtract(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.subtract(pNumber1, pNumber2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.divide(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.divide(pNumber1, pNumber2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.multiply(pNumber1, pNumber2);
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    stats.fpOperations.getAndIncrement();
    return delegate.multiply(pNumber1, pNumber2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    stats.fpOperations.getAndIncrement();
    return delegate.remainder(number1, number2);
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.assignment(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.equalWithFPSemantics(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.greaterThan(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.greaterOrEquals(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.lessThan(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    stats.fpOperations.getAndIncrement();
    return delegate.lessOrEquals(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isNaN(pNumber);
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isInfinity(pNumber);
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isZero(pNumber);
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isNormal(pNumber);
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isSubnormal(pNumber);
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula pNumber) {
    stats.fpOperations.getAndIncrement();
    return delegate.isNegative(pNumber);
  }
}
