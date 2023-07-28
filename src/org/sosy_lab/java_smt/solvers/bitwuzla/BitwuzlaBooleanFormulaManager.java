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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaBooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long
    , Long> {
  protected BitwuzlaBooleanFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
  }

  @Override
  protected Long makeVariableImpl(String pVar) {
    return null;
  }

  @Override
  protected Long makeBooleanImpl(boolean value) {
    return null;
  }

  @Override
  protected Long not(Long pParam1) {
    return null;
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return null;
  }

  @Override
  protected Long equivalence(Long bits1, Long bits2) {
    return null;
  }

  @Override
  protected boolean isTrue(Long bits) {
    return false;
  }

  @Override
  protected boolean isFalse(Long bits) {
    return false;
  }

  @Override
  protected Long ifThenElse(Long cond, Long f1, Long f2) {
    return null;
  }
}
