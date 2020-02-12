/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;

@RunWith(Parameterized.class)
public class SolverContextTest extends SolverBasedTest0 {

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
  public void testMultipleContextClose() {
    context.close();
    context.close();
    context.close();
    context.close();
  }

  @Test
  public void testFormulaAccessAfterClose() {
    BooleanFormula term = bmgr.makeVariable("variable");
    context.close();

    // after calling 'close()', it depends on the solver whether we can further access any formula.
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.MATHSAT5, Solvers.Z3, Solvers.BOOLECTOR);

    // try to access some data about formulae and managers
    assertThat(term.toString()).isEqualTo("variable");
    assertThat(bmgr.isTrue(term)).isFalse();
  }
}
