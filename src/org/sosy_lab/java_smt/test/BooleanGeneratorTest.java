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

import java.io.IOException;
import org.junit.*;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.utils.Generators.BooleanGenerator;
import org.sosy_lab.java_smt.utils.Generators.Generator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;


public class BooleanGeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0  {

  private static int i = 0;
  @Test
  public void testMakeVariable() {
    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      Generator.lines.delete(0, Generator.lines.length());
      Generator.registeredVariables.clear();
      BooleanFormula a = bmgr.makeVariable("a" + i);
      Generator.logAddConstraint(a);
      String actualResult = String.valueOf(Generator.lines);

      String expectedResult = String.format("(declare-const a%1$s Bool)\n"
          + "(assert a%1$s)\n", String.valueOf(i));
      Generator.dumpSMTLIB2();
      Assert.assertEquals(expectedResult, actualResult);
      i++;
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }
}
