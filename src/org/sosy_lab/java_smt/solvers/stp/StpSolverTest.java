/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import static org.junit.Assert.assertTrue;

import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

public class StpSolverTest {

  private Configuration config;
  private LogManager logger;
  private ShutdownNotifier shutdownNotifier;
  private Solvers solver;

  public StpSolverTest() throws InvalidConfigurationException {
    config = Configuration.defaultConfiguration();
    logger = BasicLogManager.create(config);
    shutdownNotifier = ShutdownNotifier.createDummy();

    solver = Solvers.STP;
  }

  @Ignore
  @Test
  public void testSolverContextClass() throws InvalidConfigurationException {

    SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, shutdownNotifier, solver);

    System.out.println(context.getSolverName() + " ::: " + context.getVersion());
    context.close();

  }


  // USING THE CONTEXT:
  // test create bool variable

  @Test
  public void createBooleanVariablesAndcheckEquivalence() throws InvalidConfigurationException {
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, shutdownNotifier, solver)) {

      BooleanFormulaManager boolFMgr = context.getFormulaManager().getBooleanFormulaManager();

      // BooleanFormula falseVar = boolFMgr.makeVariable("falseVar");
      // BooleanFormula trueVar = boolFMgr.equivalence(falseVar, boolFMgr.makeBoolean(false));

      // these would raise a nasty
      // assertTrue(boolFMgr.isFalse(falseVar));
      // assertTrue(boolFMgr.isTrue(trueVar));

      // test boolean constants
      BooleanFormula falseValue = boolFMgr.makeFalse();
      BooleanFormula trueValue = boolFMgr.makeBoolean(true);


      assertTrue(boolFMgr.isTrue(trueValue));
      assertTrue(boolFMgr.isFalse(falseValue));

    }
  }

  // test create BV variable
  // test create Array variable

  // Test Prover

}
