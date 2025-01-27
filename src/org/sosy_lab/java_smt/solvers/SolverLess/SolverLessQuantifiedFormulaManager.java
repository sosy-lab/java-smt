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

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;

public class SolverLessQuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessQuantifiedFormulaManager(SolverLessFormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  protected DummyFormula eliminateQuantifiers(DummyFormula pExtractInfo)
      throws SolverException, InterruptedException {
    return null;
  }

  @Override
  public DummyFormula mkQuantifier(Quantifier q, List<DummyFormula> vars, DummyFormula body) {
    return null;
  }
}
