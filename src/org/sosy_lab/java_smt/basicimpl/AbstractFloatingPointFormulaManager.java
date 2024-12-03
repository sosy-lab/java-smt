// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.base.Preconditions;
import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

/**
 * Similar to the other Abstract*FormulaManager classes in this package, this class serves as a
 * helper for implementing {@link FloatingPointFormulaManager}. It handles all the unwrapping and
 * wrapping from and to the {@link Formula} instances, such that the concrete class needs to handle
 * only its own internal types.
 *
 * <p>For {@link #multiply(FloatingPointFormula, FloatingPointFormula)}, and {@link
 * #divide(FloatingPointFormula, FloatingPointFormula)} this class even offers an implementation
 * based on UFs. Sub-classes are supposed to override them if they can implement these operations
 * more precisely (for example multiplication with constants should be supported by all solvers and
 * implemented by all sub-classes).
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements FloatingPointFormulaManager {

  private final Map<FloatingPointRoundingMode, TFormulaInfo> roundingModes;

  protected AbstractFloatingPointFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
    roundingModes = new HashMap<>();
  }

  protected abstract TFormulaInfo getDefaultRoundingMode();

  protected abstract TFormulaInfo getRoundingModeImpl(
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  private TFormulaInfo getRoundingMode(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return roundingModes.computeIfAbsent(pFloatingPointRoundingMode, this::getRoundingModeImpl);
  }

  protected FloatingPointFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateFloatingPoint(pTerm);
  }
  @Override
  public FloatingPointFormula makeNumber(Rational n, FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeNumberImpl(n.toString(), type, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }
  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(n.toString(), type, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }
  @Override
  public FloatingPointFormula makeNumber(double n, FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

  protected abstract TFormulaInfo makeNumberImpl(
      double n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

  protected TFormulaInfo makeNumberImpl(
      BigDecimal n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode) {
    return makeNumberImpl(n.toPlainString(), type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

 @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(n, type, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, type.getExponentSize(), type.getMantissaSize());
    }
    return result;
  }

  /** directly catch the most common special String constants. */
  protected TFormulaInfo makeNumberImpl(
      String n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode) {
    if (n.startsWith("+")) {
      n = n.substring(1);
    }
    switch (n) {
      case "NaN":
      case "-NaN":
        return makeNaNImpl(type);
      case "Infinity":
        return makePlusInfinityImpl(type);
      case "-Infinity":
        return makeMinusInfinityImpl(type);
      default:
        return makeNumberAndRound(n, type, pFloatingPointRoundingMode);
    }
  }

  protected static boolean isNegativeZero(Double pN) {
    Preconditions.checkNotNull(pN);
    if(Generator.isLoggingEnabled()){
      throw new GeneratorException("Logging isNegativeZero ist not supported yet");
    }
    return Double.valueOf("-0.0").equals(pN);
  }

  protected abstract TFormulaInfo makeNumberAndRound(
      String pN, FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeVariable(String pVar, FormulaType.FloatingPointType pType) {
    checkVariableName(pVar);
    FloatingPointFormula result = wrap(makeVariableImpl(pVar, pType));
    if(Generator.isLoggingEnabled()){
      FloatingPointGenerator.logMakeFloatingPointVariable(result, pType, pVar);
    }
    return result;
  }

  protected abstract TFormulaInfo makeVariableImpl(
      String pVar, FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makePlusInfinity(FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makePlusInfinityImpl(type));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakePlusInfinity(result, type);
    }
    return result;
  }

  protected abstract TFormulaInfo makePlusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeMinusInfinity(FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeMinusInfinityImpl(type));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeMinusInfinity(result, type);
    }
    return result;
  }

  protected abstract TFormulaInfo makeMinusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeNaN(FormulaType.FloatingPointType type) {
    FloatingPointFormula result = wrap(makeNaNImpl(type));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeNaN(result, type);
    }
    return result;
  }

  protected abstract TFormulaInfo makeNaNImpl(FormulaType.FloatingPointType pType);

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula number, boolean signed, FormulaType<T> targetType) {
    T result = getFormulaCreator()
        .encapsulate(
            targetType,
            castToImpl(extractInfo(number), signed, targetType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastTo(result, number, targetType.toString(), "default");
    }
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula number,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode roundingMode) {
    T result = getFormulaCreator()
        .encapsulate(
            targetType,
            castToImpl(
                extractInfo(number),
                signed,
                targetType,
                getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastTo(result, number, targetType.toString(), roundingMode.name());
    }
    return result;
  }


  protected abstract TFormulaInfo castToImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula castFrom(
      Formula number, boolean signed, FloatingPointType targetType) {
    FloatingPointFormula result = wrap(castFromImpl(extractInfo(number), signed, targetType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastFrom(result, number, "generic", "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula number,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(
        castFromImpl(
            extractInfo(number), signed, targetType, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastFrom(result, number, "generic", roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo castFromImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType.FloatingPointType pTargetType,
      TFormulaInfo pRoundingMode);


  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FloatingPointType targetType) {
    FloatingPointFormula result = wrap(fromIeeeBitvectorImpl(extractInfo(number), targetType));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFromIeeeBitvector(result, number, targetType);
    }
    return result;
  }

  protected abstract TFormulaInfo fromIeeeBitvectorImpl(
      TFormulaInfo pNumber, FloatingPointType pTargetType);

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    BitvectorFormula result = getFormulaCreator().encapsulateBitvector(toIeeeBitvectorImpl(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logToIeeeBitvector(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo toIeeeBitvectorImpl(TFormulaInfo pNumber);

  @Override
  public FloatingPointFormula negate(FloatingPointFormula n) {
    TFormulaInfo param = extractInfo(n);
    FloatingPointFormula result = wrap(negate(param));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPNegate(result, n);
    }
    return result;
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    TFormulaInfo param1 = extractInfo(number);
    FloatingPointFormula result = wrap(abs(param1));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAbs(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo abs(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    FloatingPointFormula result = wrap(max(extractInfo(number1), extractInfo(number2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMax(result, number1, number2);
    }
    return result;
  }

  protected abstract TFormulaInfo max(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula min(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    FloatingPointFormula result = wrap(min(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMin(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo min(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    FloatingPointFormula result = wrap(sqrt(extractInfo(number), getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSqrt(result, number, "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(sqrt(extractInfo(number), getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSqrt(result, number, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo sqrt(TFormulaInfo pNumber, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula add(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(add(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAdd(result, n1, n2, "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula n1, FloatingPointFormula n2, FloatingPointRoundingMode roundingMode) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(add(param1, param2, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAdd(result, n1, n2, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo add(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(subtract(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSub(result, n1, n2, "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula n1, FloatingPointFormula n2, FloatingPointRoundingMode roundingMode) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(subtract(param1, param2, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSub(result, n1, n2, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo subtract(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula divide(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(divide(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPDiv(result, n1, n2, "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula n1, FloatingPointFormula n2, FloatingPointRoundingMode roundingMode) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(divide(param1, param2, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPDiv(result, n1, n2, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo divide(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(multiply(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMul(result, n1, n2, "default");
    }
    return result;
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula n1, FloatingPointFormula n2, FloatingPointRoundingMode roundingMode) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    FloatingPointFormula result = wrap(multiply(param1, param2, getRoundingMode(roundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMul(result, n1, n2, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo multiply(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    BooleanFormula result = wrapBool(assignment(extractInfo(number1), extractInfo(number2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAssignment(result, number1, number2);
    }
    return result;
  }

  protected abstract TFormulaInfo assignment(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    BooleanFormula result = wrapBool(equalWithFPSemantics(extractInfo(number1), extractInfo(number2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPEqual(result, number1, number2);
    }
    return result;
  }

  protected abstract TFormulaInfo equalWithFPSemantics(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    BooleanFormula result = wrapBool(greaterThan(param1, param2));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPGreaterThan(result, n1, n2);
    }
    return result;
  }


  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    BooleanFormula result = wrapBool(greaterOrEquals(extractInfo(number1), extractInfo(number2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPGreaterOrEquals(result, number1, number2);
    }
    return result;
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(FloatingPointFormula n1, FloatingPointFormula n2) {
    TFormulaInfo param1 = extractInfo(n1);
    TFormulaInfo param2 = extractInfo(n2);
    BooleanFormula result = wrapBool(lessThan(param1, param2));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPLessThan(result, n1, n2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    BooleanFormula result = wrapBool(lessOrEquals(extractInfo(number1), extractInfo(number2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPLessOrEquals(result, number1, number2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isNaN(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNaN(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isNaN(TFormulaInfo pParam);

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isInfinity(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsInfinite(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isInfinity(TFormulaInfo pParam);

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isZero(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsZero(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isZero(TFormulaInfo pParam);

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isSubnormal(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsSubnormal(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isSubnormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isNormal(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNormal(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isNormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    BooleanFormula result = wrapBool(isNegative(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNegative(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo isNegative(TFormulaInfo pParam);

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    FloatingPointFormula result = wrap(round(extractInfo(number), roundingMode));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPRound(result, number, roundingMode.name());
    }
    return result;
  }

  protected abstract TFormulaInfo round(
      TFormulaInfo pFormula, FloatingPointRoundingMode pRoundingMode);


}
