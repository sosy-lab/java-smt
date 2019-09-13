/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_add;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_eq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_geq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_gt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_leq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_lt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_distinct;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_floor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_neg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_float;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sub;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_arithmetic;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

abstract class Yices2NumeralFormulaManager<ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends
    AbstractNumeralFormulaManager<Integer, Integer, Long, ParamFormulaType, ResultFormulaType, Integer> {

  protected Yices2NumeralFormulaManager(
      Yices2FormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected boolean isNumeral(Integer pVal) {
    // TODO Auto-generated method stub
    return yices_term_is_arithmetic(pVal);
  }

  @Override
  public Integer makeNumberImpl(long pI) {
    // TODO Auto-generated method stub
    int n = (int) pI;
    if (n == pI) {
      return yices_int32(n);
    }
    return yices_int64(pI);
  }

  @Override
  public Integer makeNumberImpl(BigInteger pI) {
    // TODO Makes either int or real. Ideal solution would be yizes_mpz
    return yices_parse_rational(pI.toString());
  }

  @Override
  public Integer makeNumberImpl(String pI) {
    // TODO Makes either int or real. Ideal solution would be yizes_mpz
    // TODO remove if not needed
    int unused = yices_parse_rational("1/2");
    return yices_parse_float(pI);
  }

  /*
   * @Override public Integer makeNumberImpl(double pNumber) { // TODO Auto-generated method stub
   * return null; }
   *
   * @Override public Integer makeNumberImpl(BigDecimal pNumber) { // TODO Auto-generated method
   * stub return null; }
   */

  protected abstract int getNumeralType();

  @Override
  public Integer makeVariableImpl(String pI) {
    // TODO Might not work? Implemented like Mathsat5
    return getFormulaCreator().makeVariable(getNumeralType(), pI);
  }

  @Override
  public Integer negate(Integer pParam1) {
    // TODO Auto-generated method stub
    return yices_neg(pParam1);
  }

  @Override
  public Integer add(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_add(pParam1, pParam2);
  }

  @Override
  public Integer subtract(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_sub(pParam1, pParam2);
  }

  @Override
  public Integer multiply(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_mul(pParam1, pParam2);
  }

  @Override
  public Integer equal(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_arith_eq_atom(pParam1, pParam2);
  }

  @Override
  public Integer distinctImpl(List<Integer> pNumbers) {
    // TODO Auto-generated method stub
    int size = pNumbers.size();
    int[] numberTerms = new int[size];
    for (int i = 0; i < size; i++) {
      numberTerms[i] = pNumbers.get(i);
    }
    return yices_distinct(size, numberTerms);
  }

  @Override
  public Integer greaterThan(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_arith_gt_atom(pParam1, pParam2);
  }

  @Override
  public Integer greaterOrEquals(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_arith_geq_atom(pParam1, pParam2);
  }

  @Override
  public Integer lessThan(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_arith_lt_atom(pParam1, pParam2);
  }

  @Override
  public Integer lessOrEquals(Integer pParam1, Integer pParam2) {
    // TODO Auto-generated method stub
    return yices_arith_leq_atom(pParam1, pParam2);
  }

  @Override
  protected Integer floor(Integer pNumber) {
    return yices_floor(pNumber);
  }
}
