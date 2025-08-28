// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_add;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_eq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_geq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_gt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_leq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_lt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_distinct;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_floor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_neg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_float;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sub;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;

import com.google.common.primitives.Ints;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class Yices2NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Integer, Integer, Long, ParamFormulaType, ResultFormulaType, Integer> {

  protected Yices2NumeralFormulaManager(
      Yices2FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected boolean isNumeral(Integer pVal) {
    return yices_term_constructor(pVal) == YICES_ARITH_CONST;
  }

  @Override
  public Integer makeNumberImpl(long pI) {
    return yices_int64(pI);
  }

  @Override
  public Integer makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  public Integer makeNumberImpl(String pI) {
    if (pI.contains("/")) {
      return yices_parse_rational(pI);
    } else {
      return yices_parse_float(pI);
    }
  }

  protected abstract int getNumeralType();

  @Override
  public Integer makeVariableImpl(String pI) {
    return getFormulaCreator().makeVariable(getNumeralType(), pI);
  }

  @Override
  public Integer negate(Integer pParam1) {
    return yices_neg(pParam1);
  }

  @Override
  public Integer add(Integer pParam1, Integer pParam2) {
    return yices_add(pParam1, pParam2);
  }

  @Override
  public Integer subtract(Integer pParam1, Integer pParam2) {
    return yices_sub(pParam1, pParam2);
  }

  @Override
  public Integer multiply(Integer pParam1, Integer pParam2) {
    if (isNumeral(pParam1) || isNumeral(pParam2)) {
      return yices_mul(pParam1, pParam2);
    } else {
      return super.multiply(pParam1, pParam2);
    }
  }

  @Override
  public Integer equal(Integer pParam1, Integer pParam2) {
    return yices_arith_eq_atom(pParam1, pParam2);
  }

  @Override
  public Integer distinctImpl(List<Integer> pNumbers) {
    if (pNumbers.size() < 2) {
      return yices_true();
    } else {
      return yices_distinct(pNumbers.size(), Ints.toArray(pNumbers));
    }
  }

  @Override
  public Integer greaterThan(Integer pParam1, Integer pParam2) {
    return yices_arith_gt_atom(pParam1, pParam2);
  }

  @Override
  public Integer greaterOrEquals(Integer pParam1, Integer pParam2) {
    return yices_arith_geq_atom(pParam1, pParam2);
  }

  @Override
  public Integer lessThan(Integer pParam1, Integer pParam2) {
    return yices_arith_lt_atom(pParam1, pParam2);
  }

  @Override
  public Integer lessOrEquals(Integer pParam1, Integer pParam2) {
    return yices_arith_leq_atom(pParam1, pParam2);
  }

  @Override
  protected Integer floor(Integer pNumber) {
    return yices_floor(pNumber);
  }

  @Override
  public Integer toRational(Integer formula) {
    return formula;
  }
}
