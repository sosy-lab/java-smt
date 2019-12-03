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
package org.sosy_lab.java_smt.solvers.opensmt2;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class OpensmtBooleanFormatManager extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  // TODO: 4. IMPLEMENT
  @SuppressWarnings("unused")
  private final long opensmtEnv;

  protected OpensmtBooleanFormatManager(OpensmtFormulaCreator pCreator) {
    super(pCreator);
    this.opensmtEnv = pCreator.getEnv();
  }

  @Override
  protected Long makeVariableImpl(String pVar) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long not(Long pParam1) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected boolean isTrue(Long pBits) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  protected boolean isFalse(Long pBits) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    // TODO Auto-generated method stub
    return null;
  }
}
