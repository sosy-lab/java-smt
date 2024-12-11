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

package org.sosy_lab.java_smt.solvers.Solverless;

import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.basicimpl.*;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessFormulaManager
    extends AbstractFormulaManager<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> {

  protected SolverLessFormulaManager(SolverLessFormulaCreator pCreator,
                                     SolverLessBooleanFormulaManager bmgr) {
    super(
        pCreator,
        new SolverLessUFManager(pCreator),
        bmgr,
        null,
        null,
        new SolverLessBitvectorFormulaManager(pCreator, bmgr),
        new SolverLessFloatingPointFormulaManager(pCreator),
        null,
        new SolverLessArrayFormulaManager(pCreator),
        null,
        new SolverLessStringFormulaManager(pCreator),
        null
    );
  }

  @Override
  public Appender dumpFormula(DummyFormula formula) {
    return null;
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    return null;
  }
}

