/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.mk_div;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_eq;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_mod;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_mul;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_true;

import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;

class Z3IntegerFormulaManager extends Z3NumeralFormulaManager<IntegerFormula, IntegerFormula> {

  Z3IntegerFormulaManager(
      Z3FormulaCreator pCreator,
      Z3FunctionFormulaManager pFunctionManager,
      boolean useNonLinearArithmetic) {
    super(pCreator, pFunctionManager, useNonLinearArithmetic);
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
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
  public Long linearModulo(Long pNumber1, Long pNumber2) {
    assert isNumeral(pNumber2);
    return nonLinearModulo(pNumber1, pNumber2);
  }

  @Override
  public Long nonLinearModulo(Long pNumber1, Long pNumber2) {
    return mk_mod(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (pModulo > 0) {
      long n = makeNumberImpl(pModulo);
      long x = subtract(pNumber1, pNumber2);
      return mk_eq(z3context, x, mk_mul(z3context, n, mk_div(z3context, x, n)));
    }
    return mk_true(z3context);
  }
}
