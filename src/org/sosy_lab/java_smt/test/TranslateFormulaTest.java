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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
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
    List<Solvers> solvers = ImmutableList.copyOf(Solvers.values());
    return Lists.transform(Lists.cartesianProduct(solvers, solvers), List::toArray);
  }

  @Before
  public void initSolvers() throws InvalidConfigurationException {
    Configuration empty =
        Configuration.builder().setOption("solver.useAntlrParser", "true").build();
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

  private void requireParserTo() {
    assume()
        .withMessage("Solver %s does not support parsing formulae", translateTo)
        .that(translateTo)
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.YICES2, Solvers.CVC5);

    assume()
        .withMessage(
            "Solver %s segfaults when parsing short queries or reports invalid length", translateTo)
        .that(translateTo)
        .isNotEqualTo(Solvers.Z3_WITH_INTERPOLATION);
  }

  private void requireParserFrom() {
    assume()
        .withMessage("Solver %s does not support parsing formulae", translateFrom)
        .that(translateFrom)
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.YICES2, Solvers.CVC5);

    assume()
        .withMessage(
            "Solver %s segfaults when parsing short queries or reports invalid length",
            translateFrom)
        .that(translateFrom)
        .isNotEqualTo(Solvers.Z3_WITH_INTERPOLATION);
  }

  private void requireIntegers() {
    assume()
        .withMessage("Solver %s does not support integer theory", translateFrom)
        .that(translateFrom)
        .isNoneOf(Solvers.BOOLECTOR, Solvers.BITWUZLA);
    assume()
        .withMessage("Solver %s does not support integer theory", translateTo)
        .that(translateTo)
        .isNoneOf(Solvers.BOOLECTOR, Solvers.BITWUZLA);
  }

  @Test
  public void testDumpingAndParsing() throws SolverException, InterruptedException {
    requireParserTo();

    BooleanFormula input = createTestFormula(managerFrom);
    String out = managerFrom.dumpFormula(input).toString();
    BooleanFormula parsed = managerTo.parse(out);

    assertUsing(to).that(createTestFormula(managerTo)).isEquivalentTo(parsed);
  }

  @Test
  public void testTranslating() throws SolverException, InterruptedException {
    requireParserTo();

    BooleanFormula inputFrom = createTestFormula(managerFrom);
    BooleanFormula inputTo = createTestFormula(managerTo);
    BooleanFormula translatedInput = managerTo.translateFrom(inputFrom, managerFrom);

    assertUsing(to).that(inputTo).isEquivalentTo(translatedInput);
  }

  @Test
  public void testTranslatingForIContextIdentity() throws SolverException, InterruptedException {
    requireIntegers();
    assume().that(translateTo).isEqualTo(translateFrom);
    FormulaManager manager = managerFrom;

    BooleanFormula inputFrom = createTestFormula(manager);
    BooleanFormula inputTo = createTestFormula(manager);
    BooleanFormula translatedInput = manager.translateFrom(inputFrom, manager);

    assertUsing(to).that(inputTo).isEquivalentTo(translatedInput);
  }

  @Test
  public void testTranslatingForContextSibling() throws SolverException, InterruptedException {
    requireIntegers();
    assume().that(translateTo).isEqualTo(translateFrom);

    assume()
        .withMessage("Solver does not support shared terms or dump/parse")
        .that(translateTo)
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    BooleanFormula inputFrom = createTestFormula(managerFrom);
    BooleanFormula inputTo = createTestFormula(managerTo);
    BooleanFormula translatedInput = managerTo.translateFrom(inputFrom, managerFrom);

    assertUsing(to).that(inputTo).isEquivalentTo(translatedInput);
  }

  @Test
  public void testTranslatingAndReverse() throws SolverException, InterruptedException {
    requireParserTo();
    requireParserFrom();

    BooleanFormula inputFrom = createTestFormula(managerFrom);
    BooleanFormula translatedInput = managerTo.translateFrom(inputFrom, managerFrom);
    BooleanFormula translatedReverseInput = managerFrom.translateFrom(translatedInput, managerTo);

    assertUsing(from).that(inputFrom).isEquivalentTo(translatedReverseInput);
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
