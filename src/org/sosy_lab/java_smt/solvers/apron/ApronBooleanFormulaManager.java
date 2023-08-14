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

import apron.Environment;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;

public class ApronBooleanFormulaManager extends AbstractBooleanFormulaManager<ApronNode,
    ApronFormulaType, Environment, Long> {

  private ApronFormulaCreator formulaCreator;
  protected ApronBooleanFormulaManager(ApronFormulaCreator pCreator) {
    super(pCreator);
    this.formulaCreator = pCreator;
  }

  @Override
  protected ApronNode makeVariableImpl(String pVar) {
    throw new UnsupportedOperationException("Apron supports only numeral variables.");
  }

  @Override
  protected ApronNode makeBooleanImpl(boolean value) {
    return null;
  }

  @Override
  protected ApronNode not(ApronNode pParam1) {
    return null;
  }

  @Override
  protected ApronNode and(ApronNode pParam1, ApronNode pParam2) {
    return null;
  }

  @Override
  protected ApronNode or(ApronNode pParam1, ApronNode pParam2) {
    return null;
  }

  @Override
  protected ApronNode xor(ApronNode pParam1, ApronNode pParam2) {
    return null;
  }

  @Override
  protected ApronNode equivalence(ApronNode bits1, ApronNode bits2) {
    return null;
  }

  @Override
  protected boolean isTrue(ApronNode bits) {
    return false;
  }

  @Override
  protected boolean isFalse(ApronNode bits) {
    return false;
  }

  @Override
  protected ApronNode ifThenElse(ApronNode cond, ApronNode f1, ApronNode f2) {
    return null;
  }
}
