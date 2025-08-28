// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_and;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_floor;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_leq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_not;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_plus;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_true;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_number;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class Mathsat5NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Long, Long, Long, ParamFormulaType, ResultFormulaType, Long> {

  final long mathsatEnv;

  Mathsat5NumeralFormulaManager(
      Mathsat5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.mathsatEnv = pCreator.getEnv();
  }

  @Override
  protected boolean isNumeral(Long val) {
    return msat_term_is_number(mathsatEnv, val);
  }

  @Override
  protected Long makeNumberImpl(long pNumber) {
    int i = (int) pNumber;
    if (i == pNumber) { // fits in an int
      return msat_make_int_number(mathsatEnv, i);
    }
    return msat_make_number(mathsatEnv, Long.toString(pNumber));
  }

  @Override
  protected Long makeNumberImpl(BigInteger pI) {
    return msat_make_number(mathsatEnv, pI.toString());
  }

  @Override
  protected Long makeNumberImpl(String pI) {
    return msat_make_number(mathsatEnv, pI);
  }

  protected abstract long getNumeralType();

  @Override
  protected Long makeVariableImpl(String var) {
    return getFormulaCreator().makeVariable(getNumeralType(), var);
  }

  @Override
  protected Long negate(Long pNumber) {
    return msat_make_times(mathsatEnv, pNumber, msat_make_number(mathsatEnv, "-1"));
  }

  @Override
  protected Long add(Long pNumber1, Long pNumber2) {
    return msat_make_plus(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long subtract(Long pNumber1, Long pNumber2) {
    return msat_make_plus(mathsatEnv, pNumber1, negate(pNumber2));
  }

  @Override
  protected Long multiply(Long pNumber1, Long pNumber2) {
    return msat_make_times(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long equal(Long pNumber1, Long pNumber2) {
    return msat_make_equal(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long distinctImpl(List<Long> pNumbers) {
    // MathSat does not directly support this method, we need to build the whole term.
    long r = msat_make_true(mathsatEnv);
    for (int i = 0; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        r = msat_make_and(mathsatEnv, r, makeNot(equal(pNumbers.get(i), pNumbers.get(j))));
      }
    }
    return r;
  }

  @Override
  protected Long greaterThan(Long pNumber1, Long pNumber2) {
    return makeNot(lessOrEquals(pNumber1, pNumber2));
  }

  @Override
  protected Long greaterOrEquals(Long pNumber1, Long pNumber2) {
    return lessOrEquals(pNumber2, pNumber1);
  }

  private long makeNot(long n) {
    return msat_make_not(mathsatEnv, n);
  }

  @Override
  protected Long lessThan(Long pNumber1, Long pNumber2) {
    return makeNot(lessOrEquals(pNumber2, pNumber1));
  }

  @Override
  protected Long lessOrEquals(Long pNumber1, Long pNumber2) {
    return msat_make_leq(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long floor(Long pNumber) {
    return msat_make_floor(mathsatEnv, pNumber);
  }

  @Override
  protected Long toRational(Long pNumber) {
    return pNumber;
  }
}
