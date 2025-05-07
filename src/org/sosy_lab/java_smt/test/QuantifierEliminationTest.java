/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.QuantifierCreationMethod.ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.QuantifierCreationMethod.ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.QuantifierEliminationMethod.ULTIMATE_ELIMINATOR;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.QuantifierEliminationMethod.ULTIMATE_ELIMINATOR_FALLBACK_ON_FAILURE;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.QuantifierEliminationMethod.ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE;

import java.util.List;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class QuantifierEliminationTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void testEliminationWithUltimateEliminator() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2, Solvers.MATHSAT5);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    // Formula: forall z, (z = x => z > y)
    BooleanFormula query =
        qmgr.forall(z, bmgr.implication(imgr.equal(z, x), imgr.greaterThan(z, y)));
    query = qmgr.eliminateQuantifiers(query, ULTIMATE_ELIMINATOR);

    assertThatFormula(query).isEquivalentTo(imgr.greaterThan(x, y));
  }

  @Test
  public void testQuantifierEliminationWithoutUltimateEliminatorNoFallbackThrowsException() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.Z3, Solvers.PRINCESS);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    // Formula: forall z, (z = x => z > y)
    BooleanFormula query =
        qmgr.forall(z, bmgr.implication(imgr.equal(z, x), imgr.greaterThan(z, y)));

    Exception exception = assertThrows(Exception.class, () -> qmgr.eliminateQuantifiers(query));

    assertThat((exception instanceof UnsupportedOperationException)).isTrue();
  }

  @Test
  public void testQuantifierEliminationWithoutUltimateEliminatorFallbackThrowsException() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.Z3, Solvers.PRINCESS, Solvers.YICES2);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    // Formula: forall z, (z = x => z > y)
    BooleanFormula query =
        qmgr.forall(z, bmgr.implication(imgr.equal(z, x), imgr.greaterThan(z, y)));

    Exception exception =
        assertThrows(
            Exception.class,
            () ->
                qmgr.eliminateQuantifiers(
                    query, ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE));

    assertThat((exception instanceof UnsupportedOperationException)).isTrue();
  }

  @Test
  public void
      testQuantifierEliminationWithoutUltimateEliminatorFallbackWithoutWarningThrowsException() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.Z3, Solvers.PRINCESS, Solvers.YICES2);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    // Formula: forall z, (z = x => z > y)
    BooleanFormula query =
        qmgr.forall(
            z,
            bmgr.implication(imgr.equal(z, x), imgr.greaterThan(z, y)),
            ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION_FALLBACK);

    Exception exception = assertThrows(Exception.class, () -> qmgr.eliminateQuantifiers(query));

    assertThat((exception instanceof UnsupportedOperationException)).isTrue();
  }

  @Test
  public void testEliminationWithUltimateEliminatorWithArray()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.MATHSAT5);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    ArrayFormula<IntegerFormula, IntegerFormula> var =
        amgr.makeArray("arr", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula query = qmgr.forall(var, imgr.equal(amgr.select(var, k), amgr.select(var, i)));

    query = qmgr.eliminateQuantifiers(query, ULTIMATE_ELIMINATOR);

    assertThatFormula(query).isEquivalentTo(imgr.equal(k, i));
  }

  @Test
  public void testEliminationWithUltimateEliminatormkWithoutQuantifier()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    ArrayFormula<IntegerFormula, IntegerFormula> var =
        amgr.makeArray("arr", FormulaType.IntegerType, FormulaType.IntegerType);

    BooleanFormula query =
        qmgr.forall(
            var,
            imgr.equal(amgr.select(var, k), amgr.select(var, i)),
            ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION);

    assertThatFormula(query).isEquivalentTo(imgr.equal(k, i));
  }

  @Test
  public void testEliminationWithUltimateEliminatormkWithoutQuantifierThrowsException() {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.MATHSAT5, Solvers.Z3, Solvers.PRINCESS);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    ArrayFormula<IntegerFormula, IntegerFormula> var =
        amgr.makeArray("arr", FormulaType.IntegerType, FormulaType.IntegerType);

    assertThrows(
        UnsupportedOperationException.class,
        () ->
            qmgr.forall(
                var,
                imgr.equal(amgr.select(var, k), amgr.select(var, i)),
                ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION));
  }

  @Test
  public void testEliminationWithoutArraysBefore() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula five = imgr.makeNumber(5);

    BooleanFormula query =
        qmgr.forall(
            k,
            bmgr.or(imgr.lessOrEquals(k, five), imgr.greaterOrEquals(k, two)),
            ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION);

    assertThatFormula(query).isSatisfiable();
  }

  @Test
  public void testQuantElimBefore() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula zero = imgr.makeNumber(0);

    BooleanFormula query =
        qmgr.forall(
            x,
            bmgr.or(
                imgr.greaterOrEquals(x, zero),
                qmgr.forall(
                    y, imgr.greaterOrEquals(y, zero), ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION)),
            ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION);

    assertThatFormula(query).isUnsatisfiable();
  }

  @Test
  public void testQuantElimNoFallback() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.MATHSAT5, Solvers.YICES2);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    // Case: Unsupported quantifier elimination
    BooleanFormula unsupportedQuery = qmgr.forall(k, imgr.equal(k, i));
    assertThatFormula(qmgr.eliminateQuantifiers(unsupportedQuery, ULTIMATE_ELIMINATOR))
        .isUnsatisfiable();
  }

  @Test
  public void testQuantElimAbort() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.Z3);

    assume()
        .withMessage(
            "Solver %s does not support parseable dumping format for UltimateEliminator " + "yet",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.YICES2);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    // Case: Unsupported quantifier elimination
    BooleanFormula unsupportedQuery = qmgr.forall(k, imgr.equal(k, i));
    Exception exception =
        assertThrows(
            Exception.class,
            () -> qmgr.eliminateQuantifiers(unsupportedQuery, ULTIMATE_ELIMINATOR));
    assertThat(
            (exception instanceof UnsupportedOperationException)
                || exception instanceof IllegalArgumentException)
        .isTrue();
  }

  @Test
  public void testQuantElimFallbackException() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.Z3, Solvers.CVC5, Solvers.CVC4);

    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula i = imgr.makeVariable("i");

    // Case: Unsupported quantifier elimination
    BooleanFormula query = qmgr.forall(k, imgr.equal(k, i));
    Exception exception =
        assertThrows(
            Exception.class,
            () ->
                qmgr.eliminateQuantifiers(
                    query, ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE));

    String expectedMessage1 =
        "UltimateEliminator failed. " + "Reverting to native " + "quantifier elimination";

    String expectedMessage2 =
        "printing without use-defines is not supported for quantified formulas";

    String expectedMessage = expectedMessage1 + expectedMessage2;

    assertThat(
            (exception instanceof UnsupportedOperationException)
                || expectedMessage.contains(exception.getMessage()))
        .isTrue();
  }

  @Test
  public void testQuantElimFallback() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();
    requireArrays();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.Z3);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);

    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(
            xx,
            bmgr.or(
                imgr.lessThan(xx, imgr.makeNumber(5)),
                imgr.lessThan(imgr.makeNumber(7), imgr.add(xx, yy))));
    BooleanFormula qFreeF =
        qmgr.eliminateQuantifiers(f, ULTIMATE_ELIMINATOR_FALLBACK_WITH_WARNING_ON_FAILURE);
    assertThatFormula(qFreeF).isEquivalentTo(imgr.lessThan(imgr.makeNumber(2), yy));
  }

  @Test
  public void testQuantElimFallbackWithoutWarning() throws SolverException, InterruptedException {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.MATHSAT5, Solvers.YICES2);

    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(
            xx,
            bmgr.or(
                imgr.lessThan(xx, imgr.makeNumber(5)),
                imgr.lessThan(imgr.makeNumber(7), imgr.add(xx, yy))));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f, ULTIMATE_ELIMINATOR_FALLBACK_ON_FAILURE);
    assertThatFormula(qFreeF).isEquivalentTo(imgr.lessThan(imgr.makeNumber(2), yy));
  }

  @Test
  public void testQuantElimFallbackNoWarnException() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not abort with given conditions", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.Z3, Solvers.CVC5, Solvers.CVC4);

    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(
            xx,
            bmgr.or(
                imgr.lessThan(xx, imgr.makeNumber(5)),
                imgr.lessThan(imgr.makeNumber(7), imgr.add(xx, yy))));

    Exception exception =
        assertThrows(
            Exception.class,
            () -> qmgr.eliminateQuantifiers(f, ULTIMATE_ELIMINATOR_FALLBACK_ON_FAILURE));

    String expectedMessage1 =
        "UltimateEliminator failed. " + "Reverting to native " + "quantifier elimination";

    String expectedMessage2 =
        "printing without use-defines is not supported for quantified formulas";

    String expectedMessage = expectedMessage1 + expectedMessage2;

    assertThat(
            (exception instanceof UnsupportedOperationException)
                || expectedMessage.contains(exception.getMessage()))
        .isTrue();
  }

  @Test
  public void testQuantElimBeforeFormulaHasNoBody() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    IntegerFormula x = imgr.makeVariable("x");

    Exception exception =
        assertThrows(
            IllegalArgumentException.class,
            () -> qmgr.forall(x, null, ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION));

    String expectedMessage = "Body is empty. Please check the input formula";

    assertThat(expectedMessage.contains(exception.getMessage())).isTrue();
  }

  @Test
  public void testQuantElimBeforeFormulaHasNoBoundVariable() {
    requireIntegers();
    requireQuantifiers();

    assume()
        .withMessage("Solver %s does not support quantifiers via JavaSMT", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assume()
        .withMessage("Solver %s does not support parsing yet", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.YICES2);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula zero = imgr.makeNumber(0);
    Exception exception =
        assertThrows(
            IllegalArgumentException.class,
            () ->
                qmgr.forall(
                    List.of(),
                    bmgr.or(
                        imgr.greaterOrEquals(x, zero),
                        qmgr.forall(
                            y,
                            imgr.greaterOrEquals(y, zero),
                            ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION)),
                    ULTIMATE_ELIMINATOR_BEFORE_FORMULA_CREATION));

    String expectedMessage = "Empty variable list for quantifier.";

    assertThat(expectedMessage.contains(exception.getMessage())).isTrue();
  }
}
