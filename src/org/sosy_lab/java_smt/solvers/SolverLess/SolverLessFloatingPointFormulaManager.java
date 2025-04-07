// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

@SuppressWarnings("StringSplitter")
public class SolverLessFloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<
        SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFloatingPointFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  protected SMTLIB2Formula getDefaultRoundingMode() {
    return new SMTLIB2Formula(new DummyType(FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));
  }

  @Override
  protected SMTLIB2Formula getRoundingModeImpl(
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(new DummyType(pFloatingPointRoundingMode));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(
      double pN, FloatingPointType pType, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(
        new DummyType(
            pType.getExponentSize(),
            pType.getMantissaSize(),
            pFloatingPointRoundingMode.getFormulaType().getRoundingMode()));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, boolean signBit, FloatingPointType type) {
    return new SMTLIB2Formula(new DummyType(type.getExponentSize(), type.getMantissaSize()));
  }

  @Override
  protected SMTLIB2Formula makeNumberAndRound(
      String pN, FloatingPointType pType, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(new DummyType(pType.getExponentSize(), pType.getMantissaSize()));
  }

  @Override
  protected SMTLIB2Formula makePlusInfinityImpl(FloatingPointType pType) {
    return new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula makeMinusInfinityImpl(FloatingPointType pType) {

    return new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula makeNaNImpl(FloatingPointType pType) {
    return new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String pVar, FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setName(pVar);
    return formula;
  }

  // Rest of the methods remain unchanged...
  @Override
  protected SMTLIB2Formula castToImpl(
      SMTLIB2Formula pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      SMTLIB2Formula pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      return new SMTLIB2Formula(targetType.getExponentSize(), targetType.getMantissaSize());
    }
    if (pTargetType.isIntegerType()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
    }
    if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      return new SMTLIB2Formula(targetType.getSize());
    }
    if (pTargetType.isRationalType()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL));
    }
    return null;
  }

  @Override
  protected SMTLIB2Formula castFromImpl(
      SMTLIB2Formula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula fromIeeeBitvectorImpl(
      SMTLIB2Formula pNumber, FloatingPointType pTargetType) {
    return new SMTLIB2Formula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula toIeeeBitvectorImpl(SMTLIB2Formula pNumber) {
    return new SMTLIB2Formula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected SMTLIB2Formula negate(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula abs(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula max(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula min(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula sqrt(SMTLIB2Formula pNumber, SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected SMTLIB2Formula add(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula subtract(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula divide(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula multiply(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula remainder(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return null;
  }

  @Override
  protected SMTLIB2Formula assignment(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula equalWithFPSemantics(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNaN(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isInfinity(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isZero(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isSubnormal(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNormal(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNegative(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula round(SMTLIB2Formula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return new SMTLIB2Formula(pFormula.getExponent(), pFormula.getMantissa());
  }
}
