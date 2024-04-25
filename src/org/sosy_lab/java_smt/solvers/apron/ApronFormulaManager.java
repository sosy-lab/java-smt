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
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;

public class ApronFormulaManager
    extends AbstractFormulaManager<ApronNode, ApronFormulaType, Environment, Long> {

  protected ApronFormulaManager(
      ApronFormulaCreator pFormulaCreator,
      ApronUFManager functionManager,
      ApronBooleanFormulaManager booleanManager,
      ApronIntegerFormulaManager pIntegerFormulaManager,
      ApronRationalFormulaManager pRationalFormulaManager) {
    super(
        pFormulaCreator,
        functionManager,
        booleanManager,
        pIntegerFormulaManager,
        pRationalFormulaManager,
        null,
        null,
        null,
        null,
        null,
        null,
        null);
  }

  public static ApronNode getTerm(Formula pFormula) {
    return ((ApronNode) pFormula).getInstance();
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    throw new UnsupportedOperationException("Apron does not support parse().");
  }

  @Override
  public Appender dumpFormula(ApronNode t) {
    throw new UnsupportedOperationException("Apron does not support dumpFormula().");
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    throw new UnsupportedOperationException("Apron does not support substitute().");
  }
}
