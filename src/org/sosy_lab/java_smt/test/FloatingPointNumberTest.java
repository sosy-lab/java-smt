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
import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;

import com.google.common.base.Strings;
import java.math.BigInteger;
import org.junit.Test;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;

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
      var fpNum =
          FloatingPointNumber.of(
              bits,
              SINGLE_PRECISION_EXPONENT_SIZE,
              SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT);
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
      var fpNum =
          FloatingPointNumber.of(
              bits,
              DOUBLE_PRECISION_EXPONENT_SIZE,
              DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT);
      assertThat(fpNum.doubleValue()).isEqualTo(d);
    }
  }

  @Test
  public void floatingPointNumberWithArbitraryPrecision() {
    var fpNum = FloatingPointNumber.of(Sign.POSITIVE, BigInteger.valueOf(10), BigInteger.ONE, 5, 7);
    assertThat(fpNum.toString()).isEqualTo("0" + "01010" + "0000001");
    assertThrows(IllegalArgumentException.class, fpNum::floatValue);
    assertThrows(IllegalArgumentException.class, fpNum::doubleValue);
  }
}
