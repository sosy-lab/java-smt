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
package org.sosy_lab.solver.test;

import com.google.common.collect.ImmutableMap;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;

@RunWith(Parameterized.class)
public class FormulaManagerTest extends SolverBasedTest0 {

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
  public void testSubstitution() throws SolverException, InterruptedException {
    BooleanFormula input =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b")),
            bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")));
    BooleanFormula out =
        mgr.substitute(
            input,
            ImmutableMap.of(
                bmgr.makeVariable("a"), bmgr.makeVariable("a1"),
                bmgr.makeVariable("b"), bmgr.makeVariable("b1"),
                bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")), bmgr.makeVariable("e")));
    assertThatFormula(out)
        .isEquivalentTo(
            bmgr.or(
                bmgr.and(bmgr.makeVariable("a1"), bmgr.makeVariable("b1")),
                bmgr.makeVariable("e")));
  }
}
