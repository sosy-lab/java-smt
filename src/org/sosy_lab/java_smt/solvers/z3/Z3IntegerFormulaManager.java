// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class Z3IntegerFormulaManager extends Z3NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  Z3IntegerFormulaManager(Z3FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected long getNumeralType() {
    return getFormulaCreator().getIntegerType();
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  /**
   * Creates an integer formula from a BigDecimal value. For Z3, we need to handle this specially to
   * avoid segfaults when dealing with decimal values that have fractional parts.
   *
   * <p>The issue is that the default implementation tries to represent decimal values as division
   * operations, which can cause segfaults in Z3 when used with integer sorts.
   *
   * <p>This method safely converts BigDecimal values by:
   * <ol>
   *   <li>Using exact conversion for integers (no fractional part)</li>
   *   <li>Truncating toward zero for values with fractional parts</li>
   * </ol>
   *
   * <p>This prevents the segfault described in issue #457.
   */
  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    if (pNumber == null) {
      return makeNumberImpl(0);
    }
    
    try {
      if (pNumber.scale() <= 0) {
        // No fractional part, safe to use the BigInteger conversion
        return makeNumberImpl(pNumber.toBigIntegerExact());
      } else {
        // For fractional parts, use integer part (truncating toward zero)
        // This avoids problems with Z3's division operations
        return makeNumberImpl(pNumber.toBigInteger());
      }
    } catch (ArithmeticException | NumberFormatException e) {
      // If any conversion fails, fall back to simple truncation
      return makeNumberImpl(pNumber.toBigInteger());
    }
  }

  @Override
  public Long modulo(Long pNumber1, Long pNumber2) {
    return Native.mkMod(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    long n = makeNumberImpl(pModulo);
    Native.incRef(z3context, n);
    try {
      return modularCongruence0(pNumber1, pNumber2, makeNumberImpl(pModulo));
    } finally {
      Native.decRef(z3context, n);
    }
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, BigInteger pModulo) {
    long n = makeNumberImpl(pModulo);
    Native.incRef(z3context, n);
    try {
      return modularCongruence0(pNumber1, pNumber2, makeNumberImpl(pModulo));
    } finally {
      Native.decRef(z3context, n);
    }
  }

  protected Long modularCongruence0(Long pNumber1, Long pNumber2, Long n) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    long x = subtract(pNumber1, pNumber2);
    Native.incRef(z3context, x);
    long div = Native.mkDiv(z3context, x, n);
    Native.incRef(z3context, div);
    long mul = Native.mkMul(z3context, 2, new long[] {n, div});
    Native.incRef(z3context, mul);
    try {
      return Native.mkEq(z3context, x, mul);
    } finally {
      Native.decRef(z3context, x);
      Native.decRef(z3context, div);
      Native.decRef(z3context, mul);
    }
  }
}
