// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.getDoublePrecisionFloatingPointType;
import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointTypeFromSizesWithHiddenBit;
import static org.sosy_lab.java_smt.api.FormulaType.getSinglePrecisionFloatingPointType;

import com.google.common.base.Strings;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.Set;
import org.junit.Test;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

public class FloatingPointNumberTest {

  @Test
  public void floatingPointNumberWithSinglePrecision() {
    for (float f :
        new float[] {
          0,
          1,
          2,
          3,
          4,
          256,
          1000,
          1024,
          -1,
          -2,
          -3,
          -4,
          -1000,
          -1024,
          Float.NEGATIVE_INFINITY,
          Float.POSITIVE_INFINITY,
          Float.MAX_VALUE,
          Float.MIN_VALUE,
          Float.MIN_NORMAL,
        }) {
      var bits = Strings.padStart(Integer.toBinaryString(Float.floatToRawIntBits(f)), 32, '0');
      var fpNum = FloatingPointNumber.of(bits, getSinglePrecisionFloatingPointType());
      assertThat(fpNum.floatValue()).isEqualTo(f);
      assertThat(fpNum.doubleValue()).isEqualTo((double) f); // float is a strict subtype of double.
    }
  }

  @Test
  public void floatingPointNumberWithDoublePrecision() {
    for (double d :
        new double[] {
          0,
          1,
          2,
          3,
          4,
          256,
          1000,
          1024,
          -1,
          -2,
          -3,
          -4,
          -1000,
          -1024,
          Double.NEGATIVE_INFINITY,
          Double.POSITIVE_INFINITY,
          Double.MAX_VALUE,
          Double.MIN_VALUE,
          Double.MIN_NORMAL,
        }) {
      var bits = Strings.padStart(Long.toBinaryString(Double.doubleToRawLongBits(d)), 64, '0');
      var fpNum = FloatingPointNumber.of(bits, getDoublePrecisionFloatingPointType());
      assertThat(fpNum.doubleValue()).isEqualTo(d);
    }
  }

  @Test
  public void floatingPointNumberWithArbitraryPrecision() {
    var fpNum =
        FloatingPointNumber.of(
            Sign.POSITIVE,
            BigInteger.valueOf(10),
            BigInteger.ONE,
            getFloatingPointTypeFromSizesWithHiddenBit(5, 8));
    assertThat(fpNum.toString()).isEqualTo("0" + "01010" + "0000001");
    assertThrows(IllegalArgumentException.class, fpNum::floatValue);
    assertThrows(IllegalArgumentException.class, fpNum::doubleValue);
  }

  private static final Set<FloatingPointType> precisionsToTest =
      ImmutableSet.of(
          getSinglePrecisionFloatingPointType(),
          getDoublePrecisionFloatingPointType(),
          getFloatingPointTypeFromSizesWithHiddenBit(8, 24),
          getFloatingPointTypeFromSizesWithHiddenBit(8, 23),
          getFloatingPointTypeFromSizesWithHiddenBit(8, 25),
          getFloatingPointTypeFromSizesWithHiddenBit(11, 53),
          getFloatingPointTypeFromSizesWithHiddenBit(11, 54),
          getFloatingPointTypeFromSizesWithHiddenBit(11, 55),
          getFloatingPointTypeFromSizesWithHiddenBit(10, 54),
          getFloatingPointTypeFromSizesWithHiddenBit(12, 54),
          getFloatingPointTypeFromSizesWithHiddenBit(7, 24),
          getFloatingPointTypeFromSizesWithHiddenBit(9, 24));

  @Test
  public void precisionToString() {
    for (FloatingPointType precisionToTest : precisionsToTest) {
      String singlePrecString = precisionToTest.toString();
      FormulaType<?> typeFromString = FormulaType.fromString(singlePrecString);
      assertThat(typeFromString.isFloatingPointType()).isTrue();
      FloatingPointType fpTypeFromString = (FloatingPointType) typeFromString;
      assertThat(fpTypeFromString.getTotalSize()).isEqualTo(precisionToTest.getTotalSize());
      assertThat(fpTypeFromString.getExponentSize()).isEqualTo(precisionToTest.getExponentSize());
      assertThat(fpTypeFromString.getMantissaSizeWithoutHiddenBit())
          .isEqualTo(precisionToTest.getMantissaSizeWithoutHiddenBit());
      assertThat(fpTypeFromString.getMantissaSizeWithHiddenBit())
          .isEqualTo(precisionToTest.getMantissaSizeWithHiddenBit());
      assertThat(typeFromString).isEqualTo(precisionToTest);
    }
  }

  @Test
  public void precisionToSMTLIB2String() {
    for (FloatingPointType precisionToTest : precisionsToTest) {
      String smtlib2StringFromPrecision = precisionToTest.toSMTLIBString();
      String expectedString1 =
          "(_ FloatingPoint "
              + precisionToTest.getExponentSize()
              + " "
              + precisionToTest.getMantissaSizeWithHiddenBit()
              + ")";
      assertThat(smtlib2StringFromPrecision).isEqualTo(expectedString1);
      // Test that output with getMantissaSizeWithoutHiddenBit + 1 == getMantissaSizeWithHiddenBit
      String expectedString2 =
          "(_ FloatingPoint "
              + precisionToTest.getExponentSize()
              + " "
              + (precisionToTest.getMantissaSizeWithoutHiddenBit() + 1)
              + ")";
      assertThat(smtlib2StringFromPrecision).isEqualTo(expectedString2);
    }
  }

  @Test
  public void singlePrecisionToSMTLIB2String() {
    String singlePrecSMTLIB2String = getSinglePrecisionFloatingPointType().toSMTLIBString();
    // We know the expected SMTLIB2 String
    assertThat(singlePrecSMTLIB2String).isEqualTo("(_ FloatingPoint 8 24)");
  }

  @Test
  public void doublePrecisionToSMTLIB2String() {
    String singlePrecSMTLIB2String = getDoublePrecisionFloatingPointType().toSMTLIBString();
    // We know the expected SMTLIB2 String
    assertThat(singlePrecSMTLIB2String).isEqualTo("(_ FloatingPoint 11 53)");
  }
}
