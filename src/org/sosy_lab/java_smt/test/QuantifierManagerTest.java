// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.StringType;

import com.google.common.collect.ImmutableList;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE", justification = "test code")
public class QuantifierManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private IntegerFormula x;
  private ArrayFormula<IntegerFormula, IntegerFormula> a;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_1;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_0;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula forall_x_a_at_x_eq_0;

  private static final int bvWidth = 16;

  private BitvectorFormula xbv;

  private ArrayFormula<BitvectorFormula, BitvectorFormula> bvArray;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula bvArray_at_x_eq_1;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula bvArray_at_x_eq_0;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula bv_forall_x_a_at_x_eq_0;

  @Before
  public void setUp() {
    requireQuantifiers();
    assume()
        .withMessage("Mathsat5 does not support quantifiers without UltimateEliminator")
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);
  }

  @Before
  public void setUpLIA() {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    x = imgr.makeVariable("x");
    a = amgr.makeArray("a", FormulaType.IntegerType, FormulaType.IntegerType);

    a_at_x_eq_1 = imgr.equal(amgr.select(a, x), imgr.makeNumber(1));
    a_at_x_eq_0 = imgr.equal(amgr.select(a, x), imgr.makeNumber(0));

    forall_x_a_at_x_eq_0 = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);
  }

  @Before
  public void setUpBV() {
    requireBitvectors();
    requireArrays();
    requireQuantifiers();

    xbv = bvmgr.makeVariable(bvWidth, "xbv");
    bvArray =
        amgr.makeArray(
            "bvArray",
            FormulaType.getBitvectorTypeWithSize(bvWidth),
            FormulaType.getBitvectorTypeWithSize(bvWidth));

    bvArray_at_x_eq_1 = bvmgr.equal(amgr.select(bvArray, xbv), bvmgr.makeBitvector(bvWidth, 1));
    bvArray_at_x_eq_0 = bvmgr.equal(amgr.select(bvArray, xbv), bvmgr.makeBitvector(bvWidth, 0));

    bv_forall_x_a_at_x_eq_0 = qmgr.forall(ImmutableList.of(xbv), bvArray_at_x_eq_0);
  }

  private SolverException handleSolverException(SolverException e) throws SolverException {
    // The tests in this class use quantifiers and thus solver failures are expected.
    // We do not ignore all SolverExceptions in order to not hide bugs,
    // but only for Princess and CVC4 which are known to not be able to solve all tests here.
    if (solverToUse() == Solvers.PRINCESS || solverToUse() == Solvers.CVC4) {
      assume().withMessage(e.getMessage()).fail();
    }
    throw e;
  }

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  @Test
  public void testLIAForallArrayConjunctUnsat()
      throws SolverException, InterruptedException, IOException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (forall x . b[x] = 0) AND (b[123] = 1) is UNSAT
    requireIntegers();

    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testBVForallArrayConjunctUnsat()
      throws SolverException, InterruptedException, IOException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (forall x . b[x] = 0) AND (b[123] = 1) is UNSAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(xbv), bvArray_at_x_eq_0),
            bvmgr.equal(
                amgr.select(bvArray, bvmgr.makeBitvector(bvWidth, 123)),
                bvmgr.makeBitvector(bvWidth, 1)));

    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testLIAForallArrayConjunctSat()
      throws SolverException, InterruptedException, IOException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (forall x . b[x] = 0) AND (b[123] = 0) is SAT
    requireIntegers();

    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));

    try {
      // CVC4 and Princess fail this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testBVForallArrayConjunctSat() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (forall x . b[x] = 0) AND (b[123] = 0) is SAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f = null;
    f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(xbv), bvArray_at_x_eq_0),
            bvmgr.equal(
                amgr.select(bvArray, bvmgr.makeBitvector(bvWidth, 123)),
                bvmgr.makeBitvector(bvWidth, 0)));
    try {
      // CVC4 and Princess fail this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIAForallArrayDisjunct1() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (forall x . b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));

    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIAForallArrayDisjunctSat2() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);
    // (forall x . b[x] = 0) OR (b[123] = 1) is SAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.or(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    try {
      // CVC4 fails this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIANotExistsArrayConjunct1() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (not exists x . not b[x] = 0) AND (b[123] = 1) is UNSAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    try {
      assertThatFormula(f).isUnsatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIANotExistsArrayConjunct2() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIANotExistsArrayConjunct3() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (not exists x . b[x] = 0) AND (b[123] = 0) is UNSAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0)),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testLIANotExistsArrayDisjunct1() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (not exists x . not b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));
    try {
      // CVC4 and Princess fail this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIANotExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) OR (b[123] = 1) is SAT
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.or(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    try {
      // CVC4 fails this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIAExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND (b[123] = 1) is SAT
    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.and(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBVExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND (b[123] = 1) is SAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f = null;
    f =
        bmgr.and(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            bvmgr.equal(
                amgr.select(bvArray, bvmgr.makeBitvector(bvWidth, 123)),
                bvmgr.makeBitvector(bvWidth, 1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testLIAExistsArrayConjunct2() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (exists x . b[x] = 1) AND  (forall x . b[x] = 0) is UNSAT

    requireIntegers();
    BooleanFormula f = null;
    f = bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_1), forall_x_a_at_x_eq_0);
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testBVExistsArrayConjunct2() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (exists x . b[x] = 1) AND (forall x . b[x] = 0) is UNSAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f = null;
    f = bmgr.and(qmgr.exists(ImmutableList.of(xbv), bvArray_at_x_eq_1), bv_forall_x_a_at_x_eq_0);
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testLIAExistsArrayConjunct3() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // (exists x . b[x] = 0) AND  (forall x . b[x] = 0) is SAT
    requireIntegers();

    BooleanFormula f = null;
    f = bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0), forall_x_a_at_x_eq_0);
    try {
      // CVC4 and Princess fail this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testBVExistsArrayConjunct3() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND (forall x . b[x] = 0) is SAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC5, Solvers.CVC4);

    BooleanFormula f = null;
    f = bmgr.and(qmgr.exists(ImmutableList.of(xbv), bvArray_at_x_eq_0), bv_forall_x_a_at_x_eq_0);
    try {
      // CVC4 and Princess fail this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testLIAExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) OR  (forall x . b[x] = 1) is SAT

    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_1));
    try {
      // Princess fails this
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testBVExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) OR (forall x . b[x] = 1) is SAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f = null;
    f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(xbv), bvArray_at_x_eq_0),
            qmgr.forall(ImmutableList.of(xbv), bvArray_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testLIAExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) OR (exists x . b[x] = 1) is SAT

    requireIntegers();
    BooleanFormula f = null;
    f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1),
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBVExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) OR (exists x . b[x] = 1) is SAT
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula f = null;
    f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(xbv), bvArray_at_x_eq_1),
            qmgr.exists(ImmutableList.of(xbv), bvArray_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testLIAContradiction() throws SolverException, InterruptedException {
    // forall x . x = x+1  is UNSAT

    requireIntegers();
    BooleanFormula f = null;
    f = qmgr.forall(ImmutableList.of(x), imgr.equal(x, imgr.add(x, imgr.makeNumber(1))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testBVContradiction() throws SolverException, InterruptedException {
    // forall x . x = x+1 is UNSAT
    requireBitvectors();

    int width = 16;
    BitvectorFormula z = bvmgr.makeVariable(width, "z");
    BooleanFormula f = null;
    f =
        qmgr.forall(
            ImmutableList.of(z), bvmgr.equal(z, bvmgr.add(z, bvmgr.makeBitvector(width, 1))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testLIASimple() throws SolverException, InterruptedException {
    // forall x . x+2 = x+1+1  is SAT
    requireIntegers();

    BooleanFormula f = null;
    f =
        qmgr.forall(
            ImmutableList.of(x),
            imgr.equal(
                imgr.add(x, imgr.makeNumber(2)),
                imgr.add(imgr.add(x, imgr.makeNumber(1)), imgr.makeNumber(1))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBVSimple() throws SolverException, InterruptedException {
    // forall z . z+2 = z+1+1 is SAT
    requireBitvectors();

    int width = 16;
    BitvectorFormula z = bvmgr.makeVariable(width, "z");
    BooleanFormula f = null;
    f =
        qmgr.forall(
            ImmutableList.of(z),
            bvmgr.equal(
                bvmgr.add(z, bvmgr.makeBitvector(width, 2)),
                bvmgr.add(
                    bvmgr.add(z, bvmgr.makeBitvector(width, 1)), bvmgr.makeBitvector(width, 1))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testLIAEquality() throws SolverException, InterruptedException {
    requireIntegers();

    // Note that due to the variable cache we simply get the existing var x here!
    IntegerFormula z = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula f = null;
    f = qmgr.forall(ImmutableList.of(z), qmgr.exists(ImmutableList.of(y), imgr.equal(z, y)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBVEquality() throws SolverException, InterruptedException {
    requireBitvectors();

    BitvectorFormula z = bvmgr.makeVariable(bvWidth, "z");
    BitvectorFormula y = bvmgr.makeVariable(bvWidth, "y");
    BooleanFormula f = null;
    f = qmgr.forall(ImmutableList.of(z), qmgr.exists(ImmutableList.of(y), bvmgr.equal(z, y)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBVEquality2() throws SolverException, InterruptedException {
    requireBitvectors();

    BitvectorFormula z = bvmgr.makeVariable(bvWidth, "z");
    BitvectorFormula y = bvmgr.makeVariable(bvWidth, "y");
    BooleanFormula f = null;
    f = qmgr.forall(ImmutableList.of(z, y), bvmgr.equal(z, y));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testBVEquality3() throws SolverException, InterruptedException {
    // exists z . (forall y . z = y && z + 2 > z)
    // UNSAT because of bv behaviour
    requireBitvectors();

    BitvectorFormula z = bvmgr.makeVariable(bvWidth, "z");
    BitvectorFormula zPlusTwo =
        bvmgr.add(bvmgr.makeVariable(bvWidth, "z"), bvmgr.makeBitvector(bvWidth, 2));
    BitvectorFormula y = bvmgr.makeVariable(bvWidth, "y");
    BooleanFormula f = null;
    f =
        qmgr.exists(
            ImmutableList.of(z),
            qmgr.forall(
                ImmutableList.of(y),
                bmgr.and(bvmgr.equal(z, y), bvmgr.greaterThan(zPlusTwo, z, false))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testLIABoundVariables() throws SolverException, InterruptedException {
    // If the free and bound vars are equal, this will be UNSAT
    requireIntegers();
    IntegerFormula aa = imgr.makeVariable("aa");
    IntegerFormula one = imgr.makeNumber(1);
    BooleanFormula restrict = bmgr.not(imgr.equal(aa, one));
    // x != 1 && exists x . (x == 1)
    BooleanFormula f = null;
    f = qmgr.exists(ImmutableList.of(aa), imgr.equal(aa, one));
    assertThatFormula(bmgr.and(f, restrict)).isSatisfiable();
  }

  @Test
  public void testBVBoundVariables() throws SolverException, InterruptedException {
    // If the free and bound vars are equal, this will be UNSAT
    requireBitvectors();

    int width = 2;
    BitvectorFormula aa = bvmgr.makeVariable(width, "aa");
    BitvectorFormula one = bvmgr.makeBitvector(width, 1);
    BooleanFormula restrict = bmgr.not(bvmgr.equal(aa, one));
    // x != 1 && exists x . (x == 1)
    BooleanFormula f = null;
    f = qmgr.exists(ImmutableList.of(aa), bvmgr.equal(aa, one));
    assertThatFormula(bmgr.and(f, restrict)).isSatisfiable();
  }

  @Test
  public void testQELight() throws InterruptedException, SolverException {
    requireIntegers();
    assume().that(solverToUse()).isEqualTo(Solvers.Z3);
    // exists y : (y=4 && x=y+3) --> simplified: x=7
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula f1 =
        qmgr.exists(
            y,
            bmgr.and(
                imgr.equal(y, imgr.makeNumber(4)), imgr.equal(x, imgr.add(y, imgr.makeNumber(3)))));
    BooleanFormula out = mgr.applyTactic(f1, Tactic.QE_LIGHT);
    assertThat(out).isEqualTo(imgr.equal(x, imgr.makeNumber(7)));
  }

  @Test
  public void testIntrospectionForall() {
    requireIntegers();
    BooleanFormula forall = null;
    forall = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);

    final AtomicBoolean isQuantifier = new AtomicBoolean(false);
    final AtomicBoolean isForall = new AtomicBoolean(false);
    final AtomicInteger numBound = new AtomicInteger(0);

    // Test introspection with visitors.
    mgr.visit(
        forall,
        new DefaultFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault(Formula f) {
            return null;
          }

          @Override
          public Void visitQuantifier(
              BooleanFormula f,
              Quantifier quantifier,
              List<Formula> boundVariables,
              BooleanFormula body) {
            isForall.set(quantifier == Quantifier.FORALL);
            isQuantifier.set(true);
            numBound.set(boundVariables.size());
            return null;
          }
        });
  }

  @Test
  public void testIntrospectionExists() {
    requireIntegers();
    BooleanFormula exists = null;
    exists = qmgr.exists(ImmutableList.of(x), a_at_x_eq_0);
    final AtomicBoolean isQuantifier = new AtomicBoolean(false);
    final AtomicBoolean isForall = new AtomicBoolean(false);
    final List<Formula> boundVars = new ArrayList<>();

    // Test introspection with visitors.
    mgr.visit(
        exists,
        new DefaultFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault(Formula f) {
            return null;
          }

          @Override
          public Void visitQuantifier(
              BooleanFormula f,
              Quantifier quantifier,
              List<Formula> boundVariables,
              BooleanFormula body) {
            assertThat(isQuantifier.get()).isFalse();
            isForall.set(quantifier == Quantifier.FORALL);
            isQuantifier.set(true);
            boundVars.addAll(boundVariables);
            return null;
          }
        });
    assertThat(isQuantifier.get()).isTrue();
    assertThat(isForall.get()).isFalse();

    assume()
        .withMessage("Quantifier introspection in JavaSMT for Princess is currently not complete.")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
    assertThat(boundVars).hasSize(1);
  }

  @Test
  public void testEmpty() {

    assume()
        .withMessage("TODO: The JavaSMT code for Princess explicitly allows this.")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    // An empty list of quantified variables throws an exception.
    assertThrows(
        IllegalArgumentException.class,
        () -> qmgr.exists(ImmutableList.of(), bmgr.makeVariable("b")));
  }

  @Test
  public void checkLIAQuantifierElimination() throws InterruptedException, SolverException {
    // build formula: (forall x . ((x < 5) | (7 < x + y)))
    // quantifier-free equivalent: (2 < y)
    requireIntegers();
    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(
            xx,
            bmgr.or(
                imgr.lessThan(xx, imgr.makeNumber(5)),
                imgr.lessThan(imgr.makeNumber(7), imgr.add(xx, yy))));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);
    assertThatFormula(qFreeF).isEquivalentTo(imgr.lessThan(imgr.makeNumber(2), yy));
  }

  @Test
  public void checkLIAQuantifierEliminationFail() throws InterruptedException, SolverException {
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // build formula: (exists x : arr[x] = 3) && (forall y: arr[y] = 2)
    // as there is no quantifier free equivalent, it should return the input formula.
    requireIntegers();
    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        amgr.makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);

    BooleanFormula f =
        bmgr.and(
            qmgr.exists(xx, imgr.equal(amgr.select(a1, xx), imgr.makeNumber(3))),
            qmgr.forall(yy, imgr.equal(amgr.select(a1, yy), imgr.makeNumber(2))));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);

    assertThatFormula(qFreeF).isEquivalentTo(f);
  }

  @Test
  public void checkBVQuantifierEliminationFail() throws InterruptedException, SolverException {
    // build formula: (exists x : arr[x] = 3) && (forall y: arr[y] = 2)
    // as there is no quantifier free equivalent, it should return the input formula.
    requireBitvectors();
    // Princess does not support bitvectors in arrays
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC5, Solvers.PRINCESS);

    int width = 2;
    BitvectorFormula xx = bvmgr.makeVariable(width, "x_bv");
    BitvectorFormula yy = bvmgr.makeVariable(width, "y_bv");
    ArrayFormula<BitvectorFormula, BitvectorFormula> array =
        amgr.makeArray(
            "array",
            FormulaType.getBitvectorTypeWithSize(width),
            FormulaType.getBitvectorTypeWithSize(width));

    BooleanFormula f =
        bmgr.and(
            qmgr.exists(xx, bvmgr.equal(amgr.select(array, xx), bvmgr.makeBitvector(width, 3))),
            qmgr.forall(yy, bvmgr.equal(amgr.select(array, yy), bvmgr.makeBitvector(width, 2))));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);

    assertThatFormula(qFreeF).isEquivalentTo(f);
  }

  @Test
  public void checkBVQuantifierElimination() throws InterruptedException, SolverException {
    requireBitvectors();

    // build formula: exists y : bv[2]. x * y = 1
    // quantifier-free equivalent: x = 1 | x = 3
    //                      or     extract_0_0 x = 1

    int i = index.getFreshId();
    int width = 2;

    BitvectorFormula xx = bvmgr.makeVariable(width, "x" + i);
    BitvectorFormula yy = bvmgr.makeVariable(width, "y" + i);
    BooleanFormula f =
        qmgr.exists(yy, bvmgr.equal(bvmgr.multiply(xx, yy), bvmgr.makeBitvector(width, 1)));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);

    assertThatFormula(qFreeF)
        .isEquivalentTo(bvmgr.equal(bvmgr.extract(xx, 0, 0), bvmgr.makeBitvector(1, 1)));
  }

  /** Quant elim test based on a crash in Z3. */
  @Test
  public void checkBVQuantifierElimination2() throws InterruptedException, SolverException {
    requireBitvectors();

    // build formula: exists a2 : (and (= a2 #x00000006)
    //                                 (= b2 #x00000006)
    //                                 (= a3 #x00000000))
    // quantifier-free equivalent: (and (= b2 #x00000006)
    //                                  (= a3 #x00000000))

    // Z3 fails this currently. Remove once thats not longer the case!
    assume().that(solverToUse()).isNotEqualTo(Solvers.Z3);
    int width = 32;

    BitvectorFormula a2 = bvmgr.makeVariable(width, "a2");
    BitvectorFormula b2 = bvmgr.makeVariable(width, "b2");
    BitvectorFormula a3 = bvmgr.makeVariable(width, "a3");

    BooleanFormula fAnd =
        bmgr.and(
            bvmgr.equal(a2, bvmgr.makeBitvector(width, 6)),
            bvmgr.equal(b2, bvmgr.makeBitvector(width, 6)),
            bvmgr.equal(a3, bvmgr.makeBitvector(width, 0)));

    BooleanFormula f = qmgr.exists(a2, fAnd);
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);

    assertThatFormula(qFreeF)
        .isEquivalentTo(
            bmgr.and(
                bvmgr.equal(b2, bvmgr.makeBitvector(width, 6)),
                bvmgr.equal(a3, bvmgr.makeBitvector(width, 0))));
  }

  @Test
  public void testExistsRestrictedRange() throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    ArrayFormula<IntegerFormula, IntegerFormula> b =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula bAtXEq1 = imgr.equal(amgr.select(b, x), imgr.makeNumber(1));
    BooleanFormula bAtXEq0 = imgr.equal(amgr.select(b, x), imgr.makeNumber(0));
    BooleanFormula exists10to20bx1 = exists(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq1);
    BooleanFormula forallXbx0 = qmgr.forall(x, bAtXEq0);

    // (exists x in [10..20] . b[x] = 1) AND (forall x . b[x] = 0) is UNSAT
    assertThatFormula(bmgr.and(exists10to20bx1, forallXbx0)).isUnsatisfiable();

    // (exists x in [10..20] . b[x] = 1) AND (b[10] = 0) is SAT
    assertThatFormula(
            bmgr.and(
                exists10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(10)), imgr.makeNumber(0))))
        .isSatisfiable();

    // (exists x in [10..20] . b[x] = 1) AND (b[1000] = 0) is SAT
    assertThatFormula(
            bmgr.and(
                exists10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(1000)), imgr.makeNumber(0))))
        .isSatisfiable();
  }

  @Test
  public void testExistsRestrictedRangeWithoutInconclusiveSolvers()
      throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.PRINCESS);

    ArrayFormula<IntegerFormula, IntegerFormula> b =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula bAtXEq1 = imgr.equal(amgr.select(b, x), imgr.makeNumber(1));
    BooleanFormula bAtXEq0 = imgr.equal(amgr.select(b, x), imgr.makeNumber(0));
    BooleanFormula exists10to20bx0 = exists(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq0);
    BooleanFormula exists10to20bx1 = exists(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq1);
    BooleanFormula forallXbx1 = qmgr.forall(x, bAtXEq1);
    BooleanFormula forallXbx0 = qmgr.forall(x, bAtXEq0);

    // (exists x in [10..20] . b[x] = 0) AND (forall x . b[x] = 0) is SAT
    assertThatFormula(bmgr.and(exists10to20bx0, forallXbx0)).isSatisfiable();

    // (exists x in [10..20] . b[x] = 1) AND (forall x . b[x] = 1) is SAT
    assertThatFormula(bmgr.and(exists10to20bx1, forallXbx1)).isSatisfiable();
  }

  @Test
  public void testForallRestrictedRange() throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    ArrayFormula<IntegerFormula, IntegerFormula> b =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula bAtXEq1 = imgr.equal(amgr.select(b, x), imgr.makeNumber(1));
    BooleanFormula bAtXEq0 = imgr.equal(amgr.select(b, x), imgr.makeNumber(0));
    BooleanFormula forall10to20bx1 = forall(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq1);

    // (forall x in [10..20] . b[x] = 1) AND (exits x in [15..17] . b[x] = 0) is UNSAT
    assertThatFormula(
            bmgr.and(forall10to20bx1, exists(x, imgr.makeNumber(15), imgr.makeNumber(17), bAtXEq0)))
        .isUnsatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND b[10] = 0 is UNSAT
    assertThatFormula(
            bmgr.and(
                forall10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(10)), imgr.makeNumber(0))))
        .isUnsatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND b[20] = 0 is UNSAT
    assertThatFormula(
            bmgr.and(
                forall10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(20)), imgr.makeNumber(0))))
        .isUnsatisfiable();
  }

  @Test
  public void testForallRestrictedRangeWithoutConclusiveSolvers()
      throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support the complete theory of quantifiers", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.PRINCESS);

    ArrayFormula<IntegerFormula, IntegerFormula> b =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula bAtXEq1 = imgr.equal(amgr.select(b, x), imgr.makeNumber(1));
    BooleanFormula bAtXEq0 = imgr.equal(amgr.select(b, x), imgr.makeNumber(0));
    BooleanFormula forall10to20bx0 = forall(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq0);
    BooleanFormula forall10to20bx1 = forall(x, imgr.makeNumber(10), imgr.makeNumber(20), bAtXEq1);

    // (forall x in [10..20] . b[x] = 0) AND (forall x . b[x] = 0) is SAT
    assertThatFormula(bmgr.and(forall10to20bx0, qmgr.forall(x, bAtXEq0))).isSatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND b[9] = 0 is SAT
    assertThatFormula(
            bmgr.and(
                forall10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(9)), imgr.makeNumber(0))))
        .isSatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND b[21] = 0 is SAT
    assertThatFormula(
            bmgr.and(
                forall10to20bx1,
                imgr.equal(amgr.select(b, imgr.makeNumber(21)), imgr.makeNumber(0))))
        .isSatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND (forall x in [0..20] . b[x] = 0) is UNSAT
    assertThatFormula(
            bmgr.and(forall10to20bx1, forall(x, imgr.makeNumber(0), imgr.makeNumber(20), bAtXEq0)))
        .isUnsatisfiable();

    // (forall x in [10..20] . b[x] = 1) AND (forall x in [0..9] . b[x] = 0) is SAT
    assertThatFormula(
            bmgr.and(forall10to20bx1, forall(x, imgr.makeNumber(0), imgr.makeNumber(9), bAtXEq0)))
        .isSatisfiable();
  }

  @Test
  public void testExistsBasicStringTheorie() throws SolverException, InterruptedException {
    requireStrings();
    requireIntegers();

    // exists var ("a" < var < "c") & length var == 1  -> var == "b"
    StringFormula stringA = smgr.makeString("a");
    StringFormula stringC = smgr.makeString("c");
    StringFormula var = smgr.makeVariable("var");

    BooleanFormula query =
        qmgr.exists(
            var,
            bmgr.and(
                imgr.equal(smgr.length(var), imgr.makeNumber(1)),
                smgr.lessThan(stringA, var),
                smgr.lessThan(var, stringC)));
    assertThatFormula(query).isSatisfiable();
  }

  @Test
  public void testForallBasicStringTheorie() throws SolverException, InterruptedException {
    requireStrings();
    requireIntegers();

    // forall var ("a" < var < "c") & length var == 1
    StringFormula stringA = smgr.makeString("a");
    StringFormula stringC = smgr.makeString("c");
    StringFormula var = smgr.makeVariable("var");

    BooleanFormula query =
        qmgr.forall(
            var,
            bmgr.and(
                imgr.equal(smgr.length(var), imgr.makeNumber(1)),
                smgr.lessThan(stringA, var),
                smgr.lessThan(var, stringC)));
    assertThatFormula(query).isUnsatisfiable();
  }

  @Test
  public void testExistsBasicStringArray() throws SolverException, InterruptedException {
    requireStrings();
    requireIntegers();

    // exists var (var = select(store(arr, 2, "bla"), 2)
    IntegerFormula two = imgr.makeNumber(2);
    StringFormula string = smgr.makeString("bla");
    StringFormula var = smgr.makeVariable("var");
    ArrayFormula<IntegerFormula, StringFormula> arr =
        amgr.makeArray("arr", FormulaType.IntegerType, StringType);
    BooleanFormula query =
        qmgr.exists(var, smgr.equal(var, amgr.select(amgr.store(arr, two, string), two)));
    assertThatFormula(query).isSatisfiable();
  }

  @Test
  public void testForallBasicStringArray() throws SolverException, InterruptedException {
    requireStrings();
    requireIntegers();

    // forall var (var = select(store(arr, 2, "bla"), 2)
    IntegerFormula two = imgr.makeNumber(2);
    StringFormula string = smgr.makeString("bla");
    StringFormula var = smgr.makeVariable("var");
    ArrayFormula<IntegerFormula, StringFormula> arr =
        amgr.makeArray("arr", FormulaType.IntegerType, StringType);
    BooleanFormula query =
        qmgr.forall(var, smgr.equal(var, amgr.select(amgr.store(arr, two, string), two)));
    assertThatFormula(query).isUnsatisfiable();
  }

  private BooleanFormula forall(
      final IntegerFormula pVariable,
      final IntegerFormula pLowerBound,
      final IntegerFormula pUpperBound,
      final BooleanFormula pBody) {
    return qmgr.forall(
        pVariable,
        bmgr.implication(
            bmgr.and(
                imgr.greaterOrEquals(pVariable, pLowerBound),
                imgr.lessOrEquals(pVariable, pUpperBound)),
            pBody));
  }

  private BooleanFormula exists(
      final IntegerFormula pVariable,
      final IntegerFormula pLowerBound,
      final IntegerFormula pUpperBound,
      final BooleanFormula pBody) {
    List<BooleanFormula> constraintsAndBody =
        ImmutableList.of(
            imgr.greaterOrEquals(pVariable, pLowerBound),
            imgr.lessOrEquals(pVariable, pUpperBound),
            pBody);
    return qmgr.exists(pVariable, bmgr.and(constraintsAndBody));
  }
}
