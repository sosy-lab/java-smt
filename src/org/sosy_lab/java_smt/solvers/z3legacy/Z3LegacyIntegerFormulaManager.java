/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.microsoft.z3legacy.Native;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class Z3LegacyIntegerFormulaManager extends Z3LegacyNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  Z3LegacyIntegerFormulaManager(Z3LegacyFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
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

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
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
