// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.MoreStrings;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

/**
 * Similar to the other Abstract*FormulaManager classes in this package, this class serves as a
 * helper for implementing {@link FloatingPointFormulaManager}. It handles all the unwrapping and
 * wrapping from and to the {@link Formula} instances, such that the concrete class needs to handle
 * only its own internal types.
 *
 * <p>For {@link #multiply(FloatingPointFormula, FloatingPointFormula)}, and {@link
 * #divide(FloatingPointFormula, FloatingPointFormula)} this class even offers an implementation
 * based on UFs. Subclasses are supposed to override them if they can implement these operations
 * more precisely (for example multiplication with constants should be supported by all solvers and
 * implemented by all subclasses).
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements FloatingPointFormulaManager {

  private final Map<FloatingPointRoundingMode, TFormulaInfo> roundingModes;

  private final AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> bvMgr;

  private final AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> bMgr;

  protected AbstractFloatingPointFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator,
      AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> pBvMgr,
      AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> pBMgr) {
    super(pCreator);
    roundingModes = new HashMap<>();
    bvMgr = pBvMgr;
    bMgr = pBMgr;
  }

  protected abstract TFormulaInfo getDefaultRoundingMode();

  protected abstract TFormulaInfo getRoundingModeImpl(
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  private TFormulaInfo getRoundingMode(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return roundingModes.computeIfAbsent(pFloatingPointRoundingMode, this::getRoundingModeImpl);
  }

  @Override
  public FloatingPointRoundingModeFormula makeRoundingMode(
      FloatingPointRoundingMode pRoundingMode) {
    return getFormulaCreator().encapsulateRoundingMode(getRoundingMode(pRoundingMode));
  }

  @Override
  public FloatingPointRoundingMode fromRoundingModeFormula(
      FloatingPointRoundingModeFormula pRoundingModeFormula) {
    return getFormulaCreator().getRoundingMode(extractInfo(pRoundingModeFormula));
  }

  /**
   * @param pTerm the term to be wrapped in a {@link FloatingPointFormula}.
   * @param pTypeForAssertions the {@link FloatingPointType} used to create pTerm. This argument is
   *     only used to verify the exponent and mantissa sizes of pTerm. Ignored if null.
   * @return input term pTerm in a {@link FloatingPointFormula}.
   */
  protected FloatingPointFormula wrapFloatingPointAndAssertType(
      TFormulaInfo pTerm, @Nullable FloatingPointType pTypeForAssertions) {
    checkArgument(
        getFormulaCreator().getFormulaType(pTerm).isFloatingPointType(),
        "Floating-Point formula %s has unexpected type: %s",
        pTerm,
        getFormulaCreator().getFormulaType(pTerm));
    if (pTypeForAssertions != null) {
      // The type derived from the term in the creator is usually built from the exponent and
      // mantissa sizes, hence comparing it to the type used to create the FP term checks that it
      // was created correctly. (There are other tests checking FP type correctness)
      checkArgument(
          getFormulaCreator().getFormulaType(pTerm).equals(pTypeForAssertions),
          "Floating-Point formula %s type %s is not equal to expected type %s",
          pTerm,
          getFormulaCreator().getFormulaType(pTerm),
          pTypeForAssertions);
    }
    return getFormulaCreator().encapsulateFloatingPoint(pTerm);
  }

  protected FloatingPointFormula wrapFloatingPoint(TFormulaInfo pTerm) {
    return wrapFloatingPointAndAssertType(pTerm, null);
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FormulaType.FloatingPointType type) {
    return wrapFloatingPointAndAssertType(
        makeNumberImpl(n.toString(), type, getDefaultRoundingMode()), type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPointAndAssertType(
        makeNumberImpl(n.toString(), type, getRoundingMode(pFloatingPointRoundingMode)), type);
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FormulaType.FloatingPointType type) {
    return wrapFloatingPointAndAssertType(makeNumberImpl(n, type, getDefaultRoundingMode()), type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPointAndAssertType(
        makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)), type);
  }

  protected abstract TFormulaInfo makeNumberImpl(
      double n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FormulaType.FloatingPointType type) {
    return wrapFloatingPointAndAssertType(makeNumberImpl(n, type, getDefaultRoundingMode()), type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPointAndAssertType(
        makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)), type);
  }

  protected TFormulaInfo makeNumberImpl(
      BigDecimal n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode) {
    return makeNumberImpl(n.toPlainString(), type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FormulaType.FloatingPointType type) {
    return wrapFloatingPointAndAssertType(makeNumberImpl(n, type, getDefaultRoundingMode()), type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPointAndAssertType(
        makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)), type);
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

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    return wrapFloatingPointAndAssertType(makeNumberImpl(exponent, mantissa, sign, type), type);
  }

  protected abstract TFormulaInfo makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type);

  protected static boolean isNegativeZero(Double pN) {
    checkNotNull(pN);
    return Double.valueOf("-0.0").equals(pN);
  }

  /**
   * Parses the provided string and converts it into a floating-point formula.
   *
   * <p>The input string must represent a valid finite floating-point number. Values such as NaN,
   * Infinity, or -Infinity are not allowed and should be handled before calling this method.
   */
  protected abstract TFormulaInfo makeNumberAndRound(
      String pN, FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeVariable(String pVar, FormulaType.FloatingPointType pType) {
    checkVariableName(pVar);
    return wrapFloatingPointAndAssertType(makeVariableImpl(pVar, pType), pType);
  }

  protected abstract TFormulaInfo makeVariableImpl(
      String pVar, FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makePlusInfinity(FormulaType.FloatingPointType pType) {
    return wrapFloatingPointAndAssertType(makePlusInfinityImpl(pType), pType);
  }

  protected abstract TFormulaInfo makePlusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeMinusInfinity(FormulaType.FloatingPointType pType) {
    return wrapFloatingPointAndAssertType(makeMinusInfinityImpl(pType), pType);
  }

  protected abstract TFormulaInfo makeMinusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeNaN(FormulaType.FloatingPointType pType) {
    return wrapFloatingPointAndAssertType(makeNaNImpl(pType), pType);
  }

  protected abstract TFormulaInfo makeNaNImpl(FormulaType.FloatingPointType pType);

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber, boolean pSigned, FormulaType<T> pTargetType) {
    return getFormulaCreator()
        .encapsulate(
            pTargetType,
            castToImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()));
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula number,
      boolean pSigned,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return getFormulaCreator()
        .encapsulate(
            targetType,
            castToImpl(
                extractInfo(number),
                pSigned,
                targetType,
                getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo castToImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula castFrom(
      Formula pNumber, boolean pSigned, FormulaType.FloatingPointType pTargetType) {
    return wrapFloatingPointAndAssertType(
        castFromImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()),
        pTargetType);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula number,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPointAndAssertType(
        castFromImpl(
            extractInfo(number), signed, targetType, getRoundingMode(pFloatingPointRoundingMode)),
        targetType);
  }

  protected abstract TFormulaInfo castFromImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType.FloatingPointType pTargetType,
      TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula pNumber, FloatingPointType pTargetType) {
    BitvectorType bvType = (BitvectorType) formulaCreator.getFormulaType(pNumber);
    checkArgument(
        bvType.getSize() == pTargetType.getTotalSize(),
        MoreStrings.lazyString(
            () ->
                String.format(
                    "The total size %s of type %s has to match the size %s of type %s.",
                    pTargetType.getTotalSize(), pTargetType, bvType.getSize(), bvType)));
    return wrapFloatingPointAndAssertType(
        fromIeeeBitvectorImpl(extractInfo(pNumber), pTargetType), pTargetType);
  }

  protected abstract TFormulaInfo fromIeeeBitvectorImpl(
      TFormulaInfo pNumber, FloatingPointType pTargetType);

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula pNumber) {
    return getFormulaCreator().encapsulateBitvector(toIeeeBitvectorImpl(extractInfo(pNumber)));
  }

  @SuppressWarnings("unused")
  protected TFormulaInfo toIeeeBitvectorImpl(TFormulaInfo pNumber) {
    throw new UnsupportedOperationException(
        "The chosen solver does not support transforming "
            + "FloatingPointFormula to IEEE bitvectors. Try using the fallback "
            + "methods toIeeeBitvector"
            + "(FloatingPointFormula, String) and/or "
            + "toIeeeBitvector(FloatingPointFormula, String, Map)");
  }

  @Override
  public BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula f, String bitvectorConstantName) {
    return toIeeeBitvector(f, bitvectorConstantName, ImmutableMap.of());
  }

  @Override
  public BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula f,
      String bitvectorConstantName,
      Map<FloatingPointFormula, BitvectorFormula> specialFPConstantHandling) {

    FormulaType.FloatingPointType fpType =
        (FloatingPointType) getFormulaCreator().getFormulaType(f);
    // The BV is sign bit + exponent + mantissa without hidden bit, which is always equal to the
    // total size as defined in SMTLIB2 with exponent + mantissa with hidden bit
    BitvectorFormula bvFormula = bvMgr.makeVariable(fpType.getTotalSize(), bitvectorConstantName);

    BooleanFormula additionalConstraint = toIeeeBitvector(f, bvFormula);

    // Build special numbers so that we can compare them in the map
    Set<FloatingPointFormula> specialNumbers =
        ImmutableSet.of(makeNaN(fpType), makePlusInfinity(fpType), makeMinusInfinity(fpType));

    BitvectorFormula toIeeeBv = bvFormula;
    for (Entry<FloatingPointFormula, BitvectorFormula> entry :
        specialFPConstantHandling.entrySet()) {
      FloatingPointFormula fpConst = entry.getKey();

      // We check that FP const special numbers are used (info from SMTLib2-standard)
      // NaN has multiple possible definitions.
      // +/- Infinity each has 2; e.g., +infinity for sort (_ FloatingPoint 2 3) is represented
      //  equivalently by (_ +oo 2 3) and (fp #b0 #b11 #b00).
      // -0 only has one representation; i.e. (_ -zero 3 2) abbreviates (fp #b1 #b000 #b0), and
      //  is therefore disallowed.
      // This automatically checks the correct type as well!
      checkArgument(
          specialNumbers.contains(fpConst),
          "You are only allowed to specify a mapping for special FP numbers with more than one"
              + " well-defined bitvector representation, i.e. NaN and +/- Infinity. Their type"
              + " has to match the type of the formula to be represented as bitvector.");

      BitvectorFormula bvTerm = entry.getValue();
      checkArgument(
          bvMgr.getLength(bvTerm) == bvMgr.getLength(bvFormula),
          "The size of the bitvector terms used as mapped values needs to be equal to the size of"
              + " the bitvector returned by this method");

      BooleanFormula assumption = assignment(fpConst, f);
      toIeeeBv = bMgr.ifThenElse(assumption, bvTerm, toIeeeBv);
    }

    return BitvectorFormulaAndBooleanFormula.of(toIeeeBv, additionalConstraint);
  }

  @Override
  public BooleanFormula toIeeeBitvector(
      FloatingPointFormula fpNumber, BitvectorFormula bitvectorFormulaSetToBeEqualToFpNumber) {
    FormulaType.FloatingPointType fpType =
        (FloatingPointType) getFormulaCreator().getFormulaType(fpNumber);
    checkArgument(
        fpType.getTotalSize() == bvMgr.getLength(bitvectorFormulaSetToBeEqualToFpNumber),
        "The size of the bitvector term %s is %s, but needs to be equal to the size of"
            + " the Floating-Point term %s with size %s",
        bitvectorFormulaSetToBeEqualToFpNumber,
        bvMgr.getLength(bitvectorFormulaSetToBeEqualToFpNumber),
        fpNumber,
        fpType.getTotalSize());

    FloatingPointFormula fromIeeeBitvector =
        fromIeeeBitvector(bitvectorFormulaSetToBeEqualToFpNumber, fpType);

    // We use assignment(), as it allows a fp value to be NaN etc.
    // Note: All fp.to_* functions are unspecified for NaN and infinity input values in the
    // standard, what solvers return might be distinct.
    return assignment(fromIeeeBitvector, fpNumber);
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrapFloatingPoint(negate(param1));
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula abs(FloatingPointFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrapFloatingPoint(abs(param1));
  }

  protected abstract TFormulaInfo abs(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula max(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    return wrapFloatingPoint(max(extractInfo(pNumber1), extractInfo(pNumber2)));
  }

  protected abstract TFormulaInfo max(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula min(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    return wrapFloatingPoint(min(extractInfo(pNumber1), extractInfo(pNumber2)));
  }

  protected abstract TFormulaInfo min(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula pNumber) {
    return wrapFloatingPoint(sqrt(extractInfo(pNumber), getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPoint(
        sqrt(extractInfo(number), getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo sqrt(TFormulaInfo pNumber, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapFloatingPoint(add(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrapFloatingPoint(
        add(
            extractInfo(number1),
            extractInfo(number2),
            getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo add(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapFloatingPoint(subtract(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);

    return wrapFloatingPoint(subtract(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo subtract(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula divide(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapFloatingPoint(divide(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);

    return wrapFloatingPoint(divide(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo divide(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapFloatingPoint(multiply(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);
    return wrapFloatingPoint(multiply(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo multiply(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return wrapFloatingPoint(remainder(extractInfo(number1), extractInfo(number2)));
  }

  protected abstract TFormulaInfo remainder(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula assignment(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(assignment(param1, param2));
  }

  protected abstract TFormulaInfo assignment(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(equalWithFPSemantics(param1, param2));
  }

  protected abstract TFormulaInfo equalWithFPSemantics(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessThan(param1, param2));
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula isNaN(FloatingPointFormula pNumber) {
    return wrapBool(isNaN(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNaN(TFormulaInfo pParam);

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula pNumber) {
    return wrapBool(isInfinity(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isInfinity(TFormulaInfo pParam);

  @Override
  public BooleanFormula isZero(FloatingPointFormula pNumber) {
    return wrapBool(isZero(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isZero(TFormulaInfo pParam);

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula pNumber) {
    return wrapBool(isSubnormal(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isSubnormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNormal(FloatingPointFormula pNumber) {
    return wrapBool(isNormal(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNegative(FloatingPointFormula pNumber) {
    return wrapBool(isNegative(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNegative(TFormulaInfo pParam);

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return wrapFloatingPoint(round(extractInfo(pFormula), pRoundingMode));
  }

  protected abstract TFormulaInfo round(
      TFormulaInfo pFormula, FloatingPointRoundingMode pRoundingMode);

  protected static String getBvRepresentation(BigInteger integer, int size) {
    char[] values = new char[size];
    for (int i = 0; i < size; i++) {
      values[size - 1 - i] = integer.testBit(i) ? '1' : '0';
    }
    return String.copyValueOf(values);
  }

  public static final class BitvectorFormulaAndBooleanFormula {
    private final BitvectorFormula bitvectorFormula;
    private final BooleanFormula booleanFormula;

    private BitvectorFormulaAndBooleanFormula(
        BitvectorFormula pBitvectorFormula, BooleanFormula pBooleanFormula) {
      bitvectorFormula = checkNotNull(pBitvectorFormula);
      booleanFormula = checkNotNull(pBooleanFormula);
    }

    private static BitvectorFormulaAndBooleanFormula of(
        BitvectorFormula pBitvectorFormula, BooleanFormula pBooleanFormula) {
      return new BitvectorFormulaAndBooleanFormula(pBitvectorFormula, pBooleanFormula);
    }

    public BitvectorFormula getBitvectorFormula() {
      return bitvectorFormula;
    }

    public BooleanFormula getBooleanFormula() {
      return booleanFormula;
    }
  }
}
