// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager.BitvectorFormulaAndBooleanFormula;

class SynchronizedFloatingPointFormulaManager implements FloatingPointFormulaManager {

  private final FloatingPointFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedFloatingPointFormulaManager(
      FloatingPointFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public FloatingPointFormula makeNumber(double pN, FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      double pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal pN, FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal pN,
      FloatingPointType pType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(String pN, FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      String pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(Rational pN, FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational pN, FloatingPointType pType, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.makeNumber(pN, pType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    synchronized (sync) {
      return delegate.makeNumber(exponent, mantissa, sign, type);
    }
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeVariable(pVar, pType);
    }
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makePlusInfinity(pType);
    }
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeMinusInfinity(pType);
    }
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType pType) {
    synchronized (sync) {
      return delegate.makeNaN(pType);
    }
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber, boolean pSigned, FormulaType<T> pTargetType) {
    synchronized (sync) {
      return delegate.castTo(pNumber, pSigned, pTargetType);
    }
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber,
      boolean pSigned,
      FormulaType<T> pTargetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.castTo(pNumber, pSigned, pTargetType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula pSource, boolean pSigned, FloatingPointType pTargetType) {
    synchronized (sync) {
      return delegate.castFrom(pSource, pSigned, pTargetType);
    }
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula pSource,
      boolean pSigned,
      FloatingPointType pTargetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.castFrom(pSource, pSigned, pTargetType, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula pNumber, FloatingPointType pTargetType) {
    synchronized (sync) {
      return delegate.fromIeeeBitvector(pNumber, pTargetType);
    }
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.toIeeeBitvector(pNumber);
    }
  }

  @Override
  public BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula number, String bitvectorConstantName) {
    synchronized (sync) {
      return delegate.toIeeeBitvector(number, bitvectorConstantName);
    }
  }

  @Override
  public BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula number,
      String bitvectorConstantName,
      Map<FloatingPointFormula, BitvectorFormula> specialFPConstantHandling) {
    synchronized (sync) {
      return delegate.toIeeeBitvector(number, bitvectorConstantName, specialFPConstantHandling);
    }
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    synchronized (sync) {
      return delegate.round(pFormula, pRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.negate(pNumber);
    }
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.abs(pNumber);
    }
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.max(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.min(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.sqrt(pNumber);
    }
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula pNumber, FloatingPointRoundingMode pRoundingMode) {
    synchronized (sync) {
      return delegate.sqrt(pNumber, pRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.add(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.add(pNumber1, pNumber2, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.subtract(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.subtract(pNumber1, pNumber2, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.divide(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.divide(pNumber1, pNumber2, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.multiply(pNumber1, pNumber2);
    }
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1,
      FloatingPointFormula pNumber2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    synchronized (sync) {
      return delegate.multiply(pNumber1, pNumber2, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    synchronized (sync) {
      return delegate.remainder(number1, number2);
    }
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.assignment(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.equalWithFPSemantics(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.greaterThan(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.greaterOrEquals(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.lessThan(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    synchronized (sync) {
      return delegate.lessOrEquals(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isNaN(pNumber);
    }
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isInfinity(pNumber);
    }
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isZero(pNumber);
    }
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isNormal(pNumber);
    }
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isSubnormal(pNumber);
    }
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.isNegative(pNumber);
    }
  }

  @Override
  public int getMantissaSize(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.getMantissaSize(pNumber);
    }
  }

  @Override
  public int getExponentSize(FloatingPointFormula pNumber) {
    synchronized (sync) {
      return delegate.getExponentSize(pNumber);
    }
  }
}
