/*
 *
 *  *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  *  This file is part of JavaSMT.
 *  *
 *  *  Copyright (C) 2007-2016  Dirk Beyer
 *  *  All rights reserved.
 *  *
 *  *  Licensed under the Apache License, Version 2.0 (the "License");
 *  *  you may not use this file except in compliance with the License.
 *  *  You may obtain a copy of the License at
 *  *
 *  *      http://www.apache.org/licenses/LICENSE-2.0
 *  *
 *  *  Unless required by applicable law or agreed to in writing, software
 *  *  distributed under the License is distributed on an "AS IS" BASIS,
 *  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  *  See the License for the specific language governing permissions and
 *  *  limitations under the License.
 *
 *
 */

package org.sosy_lab.solver.test;

import com.google.common.collect.ImmutableList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

@RunWith(Parameterized.class)
public class UFManagerTest extends SolverBasedTest0 {
  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void testDeclareAndCallUF() {
    fmgr.declareAndCallUF(
        "Func",
        FormulaType.IntegerType,
        ImmutableList.<Formula>of(
            imgr.makeNumber(1)
        )
    );
  }

  @Test
  public void testDeclareAndCallUFWithPipes() {
    fmgr.declareAndCallUF(

        // SMTInterpol escaping is too eager.
        "|Func|",
        FormulaType.IntegerType,
        ImmutableList.<Formula>of(
            imgr.makeNumber(1)
        )
    );
  }

  @Test
  public void testDeclareAndCallUFWithBrackets() {
    fmgr.declareAndCallUF(

        // SMTInterpol escaping is too eager.
        "(Func)",
        FormulaType.IntegerType,
        ImmutableList.<Formula>of(
            imgr.makeNumber(1)
        )
    );
  }

  @Test
  public void testDeclareThanCall() {
    FunctionDeclaration<IntegerFormula>
        declaration = fmgr.declareUF(
        "Func2",
        FormulaType.IntegerType,
        FormulaType.IntegerType);

    mgr.makeApplication(declaration, imgr.makeNumber(1));
    fmgr.callUF(declaration, imgr.makeNumber(2));
  }
}
