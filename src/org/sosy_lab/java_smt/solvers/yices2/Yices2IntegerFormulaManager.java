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

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_leq0_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ceil;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_division;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_floor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ite;

import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class Yices2IntegerFormulaManager extends
    Yices2NumeralFormulaManager<IntegerFormula, IntegerFormula> implements IntegerFormulaManager {

  Yices2IntegerFormulaManager(
      Yices2FormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected int getNumeralType() {
    // TODO Auto-generated method stub
    return getFormulaCreator().getIntegerType();
  }

  @Override
  protected Integer makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Integer makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  public Integer divide(Integer pParam1, Integer pParam2) {
    final int div = yices_division(pParam1, pParam2);
    return yices_ite(yices_arith_leq0_atom(pParam2), yices_ceil(div), yices_floor(div));
  }

}

