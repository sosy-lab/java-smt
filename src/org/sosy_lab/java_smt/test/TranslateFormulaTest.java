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

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.assertUsing;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/** Testing formula serialization. */
@RunWith(Parameterized.class)
public class TranslateFormulaTest {

  private final LogManager logger = LogManager.createTestLogManager();

  private SolverContext from;
  private SolverContext to;
  private FormulaManager managerFrom;
  private FormulaManager managerTo;

  @Parameter(0)
  public Solvers translateFrom;

  @Parameter(1)
  public Solvers translateTo;

  @Parameters(name = "{index}: {0} --> {1}")
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
  public void initSolvers() throws InvalidConfigurationException {
    Configuration empty = Configuration.builder().build();
    SolverContextFactory factory =
        new SolverContextFactory(empty, logger, ShutdownManager.create().getNotifier());

    try {
      from = factory.generateContext(translateFrom);
      to = factory.generateContext(translateTo);
    } catch (InvalidConfigurationException e) {
      assume()
          .withMessage(e.getMessage())
          .that(e)
          .hasCauseThat()
          .isNotInstanceOf(UnsatisfiedLinkError.class);
      throw e;
    }
    managerFrom = from.getFormulaManager();
    managerTo = to.getFormulaManager();
  }

  @After
  public void close() {
    if (from != null) {
      from.close();
    }
    if (to != null) {
      to.close();
    }
  }

  private void requireParser() {
    assume()
        .withMessage("Solver %s does not support parsing formulae", translateTo)
        .that(translateTo)
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR);
  }

  private void requireIntegers() {
    assume()
        .withMessage("Solver %s does not support integer theory", translateFrom)
        .that(translateFrom)
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  @Test
  public void testDumpingAndParsing() throws SolverException, InterruptedException {
    requireParser();

    BooleanFormula input = createTestFormula(managerFrom);
    String out = managerFrom.dumpFormula(input).toString();
    BooleanFormula parsed = managerTo.parse(out);

    assertUsing(to).that(createTestFormula(managerTo)).isEquivalentTo(parsed);
  }

  @Test
  public void testTranslating() throws SolverException, InterruptedException {
    requireParser();

    BooleanFormula input = createTestFormula(managerFrom);
    BooleanFormula parsed = managerTo.translateFrom(input, managerFrom);

    assertUsing(to).that(createTestFormula(managerTo)).isEquivalentTo(parsed);
  }

  private BooleanFormula createTestFormula(FormulaManager mgr) {
    requireIntegers();

    BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
    IntegerFormulaManager ifmgr = mgr.getIntegerFormulaManager();
    IntegerFormula x = ifmgr.makeVariable("x");
    IntegerFormula y = ifmgr.makeVariable("y");
    IntegerFormula z = ifmgr.makeVariable("z");
    BooleanFormula t =
        bfmgr.and(
            bfmgr.or(ifmgr.equal(x, y), ifmgr.equal(x, ifmgr.makeNumber(2))),
            bfmgr.or(ifmgr.equal(y, z), ifmgr.equal(z, ifmgr.makeNumber(10))));
    return t;
  }
}
