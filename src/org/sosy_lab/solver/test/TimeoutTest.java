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

import com.google.common.truth.TruthJUnit;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.Fuzzer;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;

/**
 * Check that timeout is handled gracefully
 */
@RunWith(Parameterized.class)
public class TimeoutTest extends SolverBasedTest0 {
  private Fuzzer fuzzer;
  private ShutdownManager manager;

  @Before
  public void setUp() {
    fuzzer = new Fuzzer(bmgr);
  }

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test(expected=InterruptedException.class)
  public void testTacticTimeout() throws Exception {
    TruthJUnit.assume().withFailureMessage(
        "Only Z3 has native tactics"
    ).that(solverToUse()).isAnyOf(Solvers.Z3, Solvers.Z3JAVA);

    BooleanFormula test = fuzzer.fuzz(20, 3);
    (new Thread() {
      public void run() {
        try {
          sleep(1);
          shutdownManager.requestShutdown("Test");
        } catch (InterruptedException pE) {
          throw new UnsupportedOperationException("Unexpected fail");
        }
      }
    }).run();
    BooleanFormula out = mgr.applyTactic(test, Tactic.NNF);
  }
}
