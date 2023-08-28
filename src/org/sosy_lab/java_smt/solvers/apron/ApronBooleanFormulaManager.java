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
import apron.Tcons1;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;

public class ApronBooleanFormulaManager extends AbstractBooleanFormulaManager<ApronNode,
    ApronFormulaType, Environment, Long> {

  private final ApronFormulaCreator formulaCreator;

  protected ApronBooleanFormulaManager(ApronFormulaCreator pCreator) {
    super(pCreator);
    this.formulaCreator = pCreator;
  }

  @Override
  protected ApronNode makeVariableImpl(String pVar) {
    throw new UnsupportedOperationException("Apron supports only numeral variables.");
  }
/**
 * Not directly implementable, true and false is represented by a constraint that is
 * always true (1!=0) or alway false (1==0)
 */
  @Override
  protected ApronNode makeBooleanImpl(boolean value) {
    throw new UnsupportedOperationException("Apron does not support makeBooleanImpl().");
  }

  @Override
  protected ApronNode not(ApronNode pParam1) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected ApronNode and(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected ApronNode or(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected ApronNode xor(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected ApronNode equivalence(ApronNode bits1, ApronNode bits2) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected boolean isTrue(ApronNode bits) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected boolean isFalse(ApronNode bits) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }

  @Override
  protected ApronNode ifThenElse(ApronNode cond, ApronNode f1, ApronNode f2) {
    throw new UnsupportedOperationException("Apron does not support boolean operations.");
  }
}
