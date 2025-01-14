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

import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.io.IOException;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class ParseAndRegenerateTest extends SolverBasedTest0 {

  public void tellSolver(){
    //query the smtlib outputs to the solver and see if it gets equivalent outputs
  }
  public void testWithFloats()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String file =
        "(set_logic QF_FP)\n"
        + "(declare-fun x () (_ FloatingPoint 11 23)\n"
        + "(declare-fun y () (_ FloatingPoint 11 23)\n"
        + "(assert (fp.eq (fp.add (x) (y)) 10)\n"
        + "(check-sat)\n"
        + "(get-model)";
    BooleanFormula parsed = mgr.universalParseFromString(file);
    Generator.assembleConstraint(parsed);
    String reparsed = String.valueOf(Generator.getLines());
    assert(file.equals(reparsed));
  }
}
