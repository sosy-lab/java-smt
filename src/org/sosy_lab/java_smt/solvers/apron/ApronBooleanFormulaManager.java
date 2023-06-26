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

package org.sosy_lab.java_smt.solvers.apron;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class ApronBooleanFormulaManager extends AbstractBooleanFormulaManager {
  protected ApronBooleanFormulaManager(FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Object makeVariableImpl(String pVar) {
    return null;
  }

  @Override
  protected Object makeBooleanImpl(boolean value) {
    return null;
  }

  @Override
  protected Object not(Object pParam1) {
    return null;
  }

  @Override
  protected Object and(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected Object or(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected Object xor(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected Object equivalence(Object bits1, Object bits2) {
    return null;
  }

  @Override
  protected boolean isTrue(Object bits) {
    return false;
  }

  @Override
  protected boolean isFalse(Object bits) {
    return false;
  }

  @Override
  protected Object ifThenElse(Object cond, Object f1, Object f2) {
    return null;
  }
}
