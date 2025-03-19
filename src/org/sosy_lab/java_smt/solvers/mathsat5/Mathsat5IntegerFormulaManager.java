// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_divide;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_floor;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_modular_congruence;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_leq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_term_ite;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class Mathsat5IntegerFormulaManager
    extends Mathsat5NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  // Reserved UF symbol for modulo(a,0)
  private final long modZeroUF;

  Mathsat5IntegerFormulaManager(
      Mathsat5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    modZeroUF =
        pCreator.declareUFImpl(
            "_%0", pCreator.getIntegerType(), ImmutableList.of(pCreator.getIntegerType()));
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

  private long ceil(long t) {
    final long minusOne = msat_make_number(mathsatEnv, "-1");
    return msat_make_times(
        mathsatEnv,
        msat_make_floor(mathsatEnv, msat_make_times(mathsatEnv, t, minusOne)),
        minusOne);
  }

  @Override
  public Long divide(Long pNumber1, Long pNumber2) {
    // Follow SMTLib rounding definition (http://smtlib.cs.uiowa.edu/theories-Ints.shtml):
    // (t2 <= 0) ? ceil(t1/t2) : floor(t1/t2)
    // (t2 <= 0) ? -floor(-(t1/t2)) : floor(t1/2)
    // According to Alberto Griggio, it is not worth hand-optimizing this,
    // MathSAT will simplify this to something like floor(1/t2 * t1) for linear queries anyway.
    final long div = msat_make_divide(mathsatEnv, pNumber1, pNumber2);
    return msat_make_term_ite(
        mathsatEnv,
        msat_make_leq(mathsatEnv, pNumber2, msat_make_int_number(mathsatEnv, 0)),
        ceil(div),
        msat_make_floor(mathsatEnv, div));
  }

  @Override
  protected Long modulo(Long pNumber1, Long pNumber2) {
    // The modulo can be calculated by the formula:
    //   remainder = dividend - floor(dividend/divisor)*divisor
    // However, this will fail if the divisor is zero as SMTLIB then allows the solver to return
    // any value for the remainder. We solve this by first checking the divisor and returning an
    // UF symbol "modZeroUF(dividend)" if it is zero. Otherwise, the formula is used to calculate
    // the remainder.
    return msat_make_term_ite(
        mathsatEnv,
        msat_make_equal(mathsatEnv, pNumber2, msat_make_int_number(mathsatEnv, 0)),
        getFormulaCreator().callFunctionImpl(modZeroUF, ImmutableList.of(pNumber1)),
        subtract(pNumber1, multiply(divide(pNumber1, pNumber2), pNumber2)));
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, BigInteger pModulo) {
    return modularCongruence0(pNumber1, pNumber2, pModulo.toString());
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    return modularCongruence0(pNumber1, pNumber2, Long.toString(pModulo));
  }

  protected Long modularCongruence0(Long pNumber1, Long pNumber2, String pModulo) {
    return msat_make_int_modular_congruence(mathsatEnv, pModulo, pNumber1, pNumber2);
  }
}
