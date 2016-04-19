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
package org.sosy_lab.solver.test;

import static com.google.common.truth.Truth.assert_;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.TestLogManager;
import org.sosy_lab.solver.SolverContextFactory;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.IntegerFormulaManager;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.SolverContext;

/**
 * Testing formula serialization.
 */
@RunWith(Parameterized.class)
public class TranslateFormulaTest {

  private final LogManager logger = TestLogManager.getInstance();

  private SolverContext from;
  private SolverContext to;
  private FormulaManager managerFrom;
  private FormulaManager managerTo;

  @Parameter(0)
  public Solvers translateFrom;

  @Parameter(1)
  public Solvers translateTo;

  @Parameters
  public static Object[] getSolversProduct() {
    // Every combination: translateFrom and translateTo.
    int len = Solvers.values().length;
    Solvers[][] combinations = new Solvers[len * len][2];
    for (int i = 0; i < len; i++) {
      for (int j = 0; j < len; j++) {
        combinations[i * len + j][0] = Solvers.values()[i];
        combinations[i * len + j][1] = Solvers.values()[j];
      }
    }
    return combinations;
  }

  @Before
  public void initSolvers() throws Exception {
    Configuration empty = Configuration.builder().build();
    SolverContextFactory factory =
        new SolverContextFactory(empty, logger, ShutdownManager.create().getNotifier());

    from = factory.generateContext(translateFrom);
    to = factory.generateContext(translateTo);
    managerFrom = from.getFormulaManager();
    managerTo = to.getFormulaManager();
  }

  @After
  public void close() throws Exception {
    from.close();
    to.close();
  }

  @Test
  public void testDumpingAndParsing() throws Exception {
    BooleanFormula input = createTestFormula(managerFrom);
    String out = managerFrom.dumpFormula(input).toString();
    BooleanFormula parsed = managerTo.parse(out);

    assertThatFormula(createTestFormula(managerTo), to).isEquivalentTo(parsed);
  }

  @Test
  public void testTranslating() throws Exception {
    BooleanFormula input = createTestFormula(managerFrom);
    BooleanFormula parsed = managerTo.translateFrom(input, managerFrom);

    assertThatFormula(createTestFormula(managerTo), to).isEquivalentTo(parsed);
  }

  private BooleanFormula createTestFormula(FormulaManager mgr) {
    BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
    IntegerFormulaManager ifmgr = mgr.getIntegerFormulaManager();
    IntegerFormula x, y, z;
    x = ifmgr.makeVariable("x");
    y = ifmgr.makeVariable("y");
    z = ifmgr.makeVariable("z");
    BooleanFormula t =
        bfmgr.and(
            bfmgr.or(ifmgr.equal(x, y), ifmgr.equal(x, ifmgr.makeNumber(2))),
            bfmgr.or(ifmgr.equal(y, z), ifmgr.equal(z, ifmgr.makeNumber(10))));
    return t;
  }

  protected final BooleanFormulaSubject assertThatFormula(
      BooleanFormula formula, SolverContext context) {
    return assert_().about(BooleanFormulaSubject.forSolver(context)).that(formula);
  }
}
