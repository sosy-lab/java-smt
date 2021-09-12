// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.assertUsing;

import com.google.common.collect.Lists;
import java.util.Arrays;
import java.util.List;
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
  public static List<Object[]> getSolverCombinations() {
    List<Solvers> solvers = Arrays.asList(Solvers.values());
    return Lists.transform(Lists.cartesianProduct(solvers, solvers), List::toArray);
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
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.YICES2);
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
