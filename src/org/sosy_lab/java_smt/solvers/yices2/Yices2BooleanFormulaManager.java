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

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_iff;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ite;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_xor2;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class Yices2BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2BooleanFormulaManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected Integer makeVariableImpl(String pVar) {
    int boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Integer makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return yices_true();
    } else {
      return yices_false();
    }
  }

  @Override
  protected Integer not(Integer pParam1) {
    return yices_not(pParam1);
  }

  @Override
  protected Integer and(Integer pParam1, Integer pParam2) {
    return yices_and2(pParam1, pParam2);
  }

  //  @Override
  //  protected Integer andImpl(Collection<Integer> pParams) {
  //    return yices_and(pParams.size(), Ints.toArray(pParams));
  //  }

  @Override
  protected Integer or(Integer pParam1, Integer pParam2) {
    return yices_or2(pParam1, pParam2);
  }

  //  @Override
  //  protected Integer orImpl(Collection<Integer> pParams) {
  //    return yices_or(pParams.size(), Ints.toArray(pParams));
  //  }

  @Override
  protected Integer xor(Integer pParam1, Integer pParam2) {
    return yices_xor2(pParam1, pParam2);
  }

  @Override
  protected Integer equivalence(Integer pBits1, Integer pBits2) {
    return yices_iff(pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Integer pBits) {
    // TODO Better way to get this information? Causes Error when called with variable.

    // if (yices_term_constructor(pBits) != 0) {
    // return false;
    // }
    // return (yices_bool_const_value(pBits) == true);
    // }
    return pBits.equals(yices_true());
  }
  @Override
  protected boolean isFalse(Integer pBits) {
    // TODO Better way to get this information? Causes Error when called with variable.

    // if (yices_term_constructor(pBits) != 0) {
    // return false;
    // }
    // return (yices_bool_const_value(pBits) == false);
    return pBits.equals(yices_false());
  }

  @Override
  protected Integer ifThenElse(Integer pCond, Integer pF1, Integer pF2) {
    return yices_ite(pCond, pF1, pF2);
  }
}
