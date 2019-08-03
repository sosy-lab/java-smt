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

import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BoolectorFormulaManager
    extends AbstractFormulaManager<Long, Long, BoolectorEnvironment, Long> {

  protected BoolectorFormulaManager(
      BoolectorFormulaCreator pFormulaCreator,
      BoolectorUFManager pFunctionManager,
      BoolectorBooleanFormulaManager pBooleanManager,
      BoolectorBitvectorFormulaManager pBitvectorManager,
      BoolectorArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        null,
        null,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Appender dumpFormula(Long pT) {
    // TODO Auto-generated method stub
    return null;
  }

  static long getBtorTerm(Formula pT) {
    return ((Mathsat5Formula) pT).getTerm();
  }

}
