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

package org.sosy_lab.java_smt.test;


import static com.google.common.truth.Truth.assertThat;

import java.io.IOException;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class ParseAndRegenerateTest extends SolverBasedTest0 {
  @Override
  public Solvers solverToUse() {
    return Solvers.Z3;
  }

  public void tellSolver() {
    //query the smtlib outputs to the solver and see if it gets equivalent outputs
  }

  @Test
  public void evaluateWithInts()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String input =
        "(set-logic QF_LIA)\n"
            + "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(assert (= (+ x y) 10))\n";
    BooleanFormula parsed = mgr.universalParseFromString(input);
    Generator.assembleConstraint(parsed);
    String reparsed = String.valueOf(Generator.getLines());
    assertThat(reparsed).isEqualTo(input);

  }

  @Test
  public void evaluateWithReals()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String input =
        "(set-logic QF_LRA)\n"
            + "(declare-const x Real)\n"
            + "(declare-const y Real)\n"
            + "(assert (= (+ x y) 10.0))\n";
    BooleanFormula parsed = mgr.universalParseFromString(input);
    Generator.assembleConstraint(parsed);
    String reparsed = String.valueOf(Generator.getLines());
    assertThat(reparsed).isEqualTo(input);
  }
}
