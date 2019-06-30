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
package org.sosy_lab.java_smt.solvers.boolector;

import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_and;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_cond;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_false;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_iff;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_not;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_or;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_true;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_xor;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class BoolectorBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long btor;

  BoolectorBooleanFormulaManager(BoolectorFormulaCreator pCreator) {
    super(pCreator);
    this.btor = pCreator.getEnv();
  }

  @Override
  public Long makeVariableImpl(String varName) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, varName);
  }

  @Override
  public Long makeBooleanImpl(boolean pValue) {
    long rValue;
    if (pValue) {
      rValue = boolector_true(btor);
    } else {
      rValue = boolector_false(btor);
    }
    return rValue;
  }

  @Override
  public Long not(Long pParam1) {
    return boolector_not(btor, pParam1);
  }

  @Override
  public Long and(Long pParam1, Long pParam2) {
    return boolector_and(btor, pParam1, pParam2);
  }

  @Override
  public Long or(Long pParam1, Long pParam2) {
    return boolector_or(btor, pParam1, pParam2);
  }

  @Override
  public Long xor(Long pParam1, Long pParam2) {
    return boolector_xor(btor, pParam1, pParam2);
  }

  @Override
  public Long equivalence(Long pBits1, Long pBits2) {
    return boolector_iff(btor, pBits1, pBits2);
  }

  @Override
  public boolean isTrue(Long pBits) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public boolean isFalse(Long pBits) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    return boolector_cond(btor, pCond, pF1, pF2);
  }

}
