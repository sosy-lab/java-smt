// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;


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
  public FloatingPointFormula makeNumber(Rational pN, FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN.toString(), pType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), pN.toString());
    }
    return result;
  }
  @Override
  public FloatingPointFormula makeNumber(
      Rational pN, FloatingPointType pType, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN.toString(), pType, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), pN.toString(), pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }
  @Override
  public FloatingPointFormula makeNumber(double pN, FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), String.valueOf(pN));
    }
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      double pN, FloatingPointType pType, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), String.valueOf(pN), pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo makeNumberImpl(
      double pN, FormulaType.FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeNumber(BigDecimal pN, FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), String.valueOf(pN));
    }
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal pN, FloatingPointType pType, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), String.valueOf(pN), pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected TFormulaInfo makeNumberImpl(
      BigDecimal pN, FormulaType.FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode) {
    return makeNumberImpl(pN.toPlainString(), pType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String pN, FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), pN);
    }
    return result;
  }

 @Override
  public FloatingPointFormula makeNumber(
      String pN, FloatingPointType pType, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(makeNumberImpl(pN, pType, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeFloatingPoint(result, pType.getExponentSize(),
          pType.getMantissaSize(), pN, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  /** directly catch the most common special String constants. */
  protected TFormulaInfo makeNumberImpl(
      String pN, FormulaType.FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode) {
    if (pN.startsWith("+")) {
      pN = pN.substring(1);
    }
    switch (pN) {
      case "NaN":
      case "-NaN":
        return makeNaNImpl(pType);
      case "Infinity":
        return makePlusInfinityImpl(pType);
      case "-Infinity":
        return makeMinusInfinityImpl(pType);
      default:
        return makeNumberAndRound(pN, pType, pFloatingPointRoundingMode);
    }
  }

  protected static boolean isNegativeZero(Double pN) {
    Preconditions.checkNotNull(pN);
    return Double.valueOf("-0.0").equals(pN);
  }

  protected abstract TFormulaInfo makeNumberAndRound(
      String pN, FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeVariable(String pVar, FormulaType.FloatingPointType pType) {
    AbstractFormulaManager.checkVariableName(pVar);
    FloatingPointFormula result = wrap(makeVariableImpl(pVar, pType));
    if(Generator.isLoggingEnabled()){
      FloatingPointGenerator.logMakeFloatingPointVariable(result, pType, pVar);
    }
    return result;
  }

  protected abstract TFormulaInfo makeVariableImpl(
      String pVar, FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makePlusInfinity(FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makePlusInfinityImpl(pType));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakePlusInfinity(result, pType);
    }
    return result;
  }

  protected abstract TFormulaInfo makePlusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeMinusInfinity(FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeMinusInfinityImpl(pType));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeMinusInfinity(result, pType);
    }
    return result;
  }

  protected abstract TFormulaInfo makeMinusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeNaN(FormulaType.FloatingPointType pType) {
    FloatingPointFormula result = wrap(makeNaNImpl(pType));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logMakeNaN(result, pType);
    }
    return result;
  }

  protected abstract TFormulaInfo makeNaNImpl(FormulaType.FloatingPointType pType);

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber, boolean pSigned, FormulaType<T> pTargetType) {
    T result = getFormulaCreator()
        .encapsulate(
            pTargetType,
            castToImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastTo(result, pNumber, pTargetType, pSigned);
    }
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber,
      boolean signed,
      FormulaType<T> pTargetType,
      FloatingPointRoundingMode pRoundingMode) {
    T result = getFormulaCreator()
        .encapsulate(
            pTargetType,
            castToImpl(
                extractInfo(pNumber),
                signed,
                pTargetType,
                getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastTo(result, pNumber,
          pRoundingMode.getSMTLIBFormat(), pTargetType, signed);
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
      Formula pNumber, boolean pSigned, FloatingPointType pTargetType) {
    FloatingPointFormula result = wrap(castFromImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastFrom(result, pNumber, pTargetType);
    }
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(
        castFromImpl(
            extractInfo(pNumber), pSigned, pTargetType, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastFrom(result, pNumber, pTargetType, pRoundingMode.getSMTLIBFormat());
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
      BitvectorFormula pNumber, FloatingPointType pTargetType) {
    FloatingPointFormula result = wrap(fromIeeeBitvectorImpl(extractInfo(pNumber), pTargetType));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFromIeeeBitvector(result, pNumber, pTargetType);
    }
    return result;
  }

  protected abstract TFormulaInfo fromIeeeBitvectorImpl(
      TFormulaInfo pNumber, FloatingPointType pTargetType);

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula pNumber) {
    BitvectorFormula result = getFormulaCreator().encapsulateBitvector(toIeeeBitvectorImpl(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPCastTo(result, pNumber,
          getFormulaCreator().getFormulaType(result), true);
    }
    return result;
  }

  protected abstract TFormulaInfo toIeeeBitvectorImpl(TFormulaInfo pNumber);

  @Override
  public FloatingPointFormula negate(FloatingPointFormula pN) {
    TFormulaInfo param = extractInfo(pN);
    FloatingPointFormula result = wrap(negate(param));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPNegate(result, pN);
    }
    return result;
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula abs(FloatingPointFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    FloatingPointFormula result = wrap(abs(param1));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAbs(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo abs(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula max(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    FloatingPointFormula result = wrap(max(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMax(result, pNumber1, pNumber2);
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
  public FloatingPointFormula sqrt(FloatingPointFormula pNumber) {
    FloatingPointFormula result = wrap(sqrt(extractInfo(pNumber), getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSqrt(result, pNumber);
    }
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula pNumber, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(sqrt(extractInfo(pNumber), getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSqrt(result, pNumber, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo sqrt(TFormulaInfo pNumber, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(add(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAdd(result, pNumber1, pNumber2);
    }
    return result;
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2, FloatingPointRoundingMode pRoundingMode) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(add(param1, param2, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAdd(result, pNumber1, pNumber2, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo add(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(subtract(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSub(result, pNumber1, pNumber2);
    }
    return result;
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2, FloatingPointRoundingMode pRoundingMode) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(subtract(param1, param2, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPSub(result, pNumber1, pNumber2, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo subtract(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula divide(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(divide(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPDiv(result, pNumber1, pNumber2);
    }
    return result;
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2, FloatingPointRoundingMode pRoundingMode) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(divide(param1, param2, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPDiv(result, pNumber1, pNumber2, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo divide(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(multiply(param1, param2, getDefaultRoundingMode()));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMul(result, pNumber1, pNumber2);
    }
    return result;
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2, FloatingPointRoundingMode pRoundingMode) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    FloatingPointFormula result = wrap(multiply(param1, param2, getRoundingMode(pRoundingMode)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPMul(result, pNumber1, pNumber2, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo multiply(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public BooleanFormula assignment(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    BooleanFormula result = wrapBool(assignment(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPAssignment(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo assignment(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    BooleanFormula result = wrapBool(equalWithFPSemantics(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPEqual(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo equalWithFPSemantics(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    BooleanFormula result = wrapBool(greaterThan(param1, param2));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPGreaterThan(result, pNumber1, pNumber2);
    }
    return result;
  }


  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    BooleanFormula result = wrapBool(greaterOrEquals(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPGreaterOrEquals(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    BooleanFormula result = wrapBool(lessThan(param1, param2));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPLessThan(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    BooleanFormula result = wrapBool(lessOrEquals(extractInfo(pNumber1), extractInfo(pNumber2)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPLessOrEquals(result, pNumber1, pNumber2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula isNaN(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isNaN(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNaN(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isNaN(TFormulaInfo pParam);

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isInfinity(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsInfinite(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isInfinity(TFormulaInfo pParam);

  @Override
  public BooleanFormula isZero(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isZero(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsZero(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isZero(TFormulaInfo pParam);

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isSubnormal(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsSubnormal(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isSubnormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNormal(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isNormal(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNormal(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isNormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNegative(FloatingPointFormula pNumber) {
    BooleanFormula result = wrapBool(isNegative(extractInfo(pNumber)));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPIsNegative(result, pNumber);
    }
    return result;
  }

  protected abstract TFormulaInfo isNegative(TFormulaInfo pParam);

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula pNumber, FloatingPointRoundingMode pRoundingMode) {
    FloatingPointFormula result = wrap(round(extractInfo(pNumber), pRoundingMode));
    if (Generator.isLoggingEnabled()) {
      FloatingPointGenerator.logFPRound(result, pNumber, pRoundingMode.getSMTLIBFormat());
    }
    return result;
  }

  protected abstract TFormulaInfo round(
      TFormulaInfo pFormula, FloatingPointRoundingMode pRoundingMode);


}
