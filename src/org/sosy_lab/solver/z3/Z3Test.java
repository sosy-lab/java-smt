/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.z3;

import org.junit.Test;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.test.SolverBasedTest0;

public class Z3Test extends SolverBasedTest0 {

  @Override
  protected Solvers solverToUse() {
    return Solvers.Z3;
  }

  @Test(expected = Exception.class)
  @SuppressWarnings("CheckReturnValue")
  public void testErrorHandling() throws Exception {
    // Will exit(1) without an exception handler.
    rmgr.makeNumber("not-a-number");
  }
}
