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

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/** Testing formula serialization. */
public class TranslateFormulaTest extends SolverBasedTest.ParameterizedSolverBasedTest {
  private FormulaManager managerFrom;
  private SolverContext from;
  private Solvers translateFrom;

  @BeforeEach
  public void beforeEach() {
    managerFrom = mgr;
    from = context;
    translateFrom = solver;
  }

  private void requireIntegersFrom() {
    requireIntegers();
  }

  private void requireParserFrom() {
    requireParser();
  }

  @Nested
  @DisplayName("to")
  class Translate extends SolverBasedTest.ParameterizedSolverBasedTest {
    private FormulaManager managerTo;
    private SolverContext to;
    private Solvers translateTo;

    @BeforeEach
    public void beforeEach() {
      managerTo = mgr;
      to = context;
      translateTo = solver;
    }

    private void requireIntegersTo() {
      requireIntegers();
    }

    private void requireParserTo() {
      requireParser();
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
      requireIntegersTo();
      requireIntegersFrom();
      assume().that(translateTo).isEqualTo(translateFrom);
      FormulaManager manager = managerFrom;

      BooleanFormula inputFrom = createTestFormula(manager);
      BooleanFormula inputTo = createTestFormula(manager);
      BooleanFormula translatedInput = manager.translateFrom(inputFrom, manager);

      assertUsing(to).that(inputTo).isEquivalentTo(translatedInput);
    }

    @Test
    public void testTranslatingForContextSibling() throws SolverException, InterruptedException {
      requireIntegersTo();
      requireIntegersFrom();
      assume().that(translateTo).isEqualTo(translateFrom);

      assume()
          .withMessage("Solver does not support shared terms or dump/parse")
          .that(translateTo)
          .isNoneOf(Solvers.CVC4, Solvers.YICES2);

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

    private BooleanFormula createTestFormula(FormulaManager manager) {
      requireIntegersTo();
      requireIntegersFrom();

      BooleanFormulaManager bfmgr = manager.getBooleanFormulaManager();
      IntegerFormulaManager ifmgr = manager.getIntegerFormulaManager();
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
}
