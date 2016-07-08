/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_bool_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_and;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_iff;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_not;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_or;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_term_ite;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_true;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_true;

import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;

class Mathsat5BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  protected Mathsat5BooleanFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  @Override
  public Long makeVariableImpl(String pVar) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  public Long makeBooleanImpl(boolean pValue) {
    long v;
    if (pValue) {
      v = msat_make_true(mathsatEnv);
    } else {
      v = msat_make_false(mathsatEnv);
    }

    return v;
  }

  @Override
  public Long equivalence(Long f1, Long f2) {
    return msat_make_iff(mathsatEnv, f1, f2);
  }

  @Override
  public boolean isTrue(Long t) {
    return msat_term_is_true(mathsatEnv, t);
  }

  @Override
  public boolean isFalse(Long t) {
    return msat_term_is_false(mathsatEnv, t);
  }

  @Override
  public Long ifThenElse(Long cond, Long f1, Long f2) {
    long t;
    long msatEnv = mathsatEnv;
    long f1Type = msat_term_get_type(f1);
    long f2Type = msat_term_get_type(f2);

    // ite does not allow boolean arguments
    if (!msat_is_bool_type(msatEnv, f1Type) || !msat_is_bool_type(msatEnv, f2Type)) {
      t = msat_make_term_ite(msatEnv, cond, f1, f2);
    } else {
      t =
          msat_make_and(
              msatEnv,
              msat_make_or(msatEnv, msat_make_not(msatEnv, cond), f1),
              msat_make_or(msatEnv, cond, f2));
    }
    return t;
  }

  @Override
  public Long not(Long pBits) {
    return msat_make_not(mathsatEnv, pBits);
  }

  @Override
  public Long and(Long pBits1, Long pBits2) {
    return msat_make_and(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long or(Long pBits1, Long pBits2) {
    return msat_make_or(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long xor(Long pBits1, Long pBits2) {
    return not(msat_make_iff(mathsatEnv, pBits1, pBits2));
  }
}
