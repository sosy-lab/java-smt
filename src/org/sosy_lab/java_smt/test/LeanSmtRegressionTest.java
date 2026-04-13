// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** LeanSMT-specific regression tests beyond generic cross-solver test suites. */
public class LeanSmtRegressionTest extends SolverBasedTest0 {

  @Override
  protected Solvers solverToUse() {
    return Solvers.LEANSMT;
  }

  @Test
  public void unsupportedOperationsAreExplicit() throws SolverException, InterruptedException {
    assertThrows(
        UnsupportedOperationException.class, () -> context.newOptimizationProverEnvironment());
    assertThrows(
        UnsupportedOperationException.class, () -> context.newProverEnvironmentWithInterpolation());
  }

  @Test
  public void bigIntegerModelEvaluation() throws SolverException, InterruptedException {
    requireIntegers();
    requireModel();

    BigInteger big = new BigInteger("987654321098765432109876543210987654321");
    IntegerFormula x = imgr.makeVariable("x_big_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(x, imgr.makeNumber(big)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(big);
      }
    }
  }

  @Test
  public void negativeIntegerModelEvaluation() throws SolverException, InterruptedException {
    requireIntegers();
    requireModel();

    BigInteger value = BigInteger.valueOf(-10);
    IntegerFormula x = imgr.makeVariable("x_neg_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(x, imgr.makeNumber(value)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(x)).isEqualTo(value);
      }
    }
  }

  @Test
  public void bigRationalModelEvaluation() throws SolverException, InterruptedException {
    requireRationals();
    requireModel();

    BigInteger bigNum = new BigInteger("111111111111111111111111111111111111111");
    Rational bigRat = Rational.of(bigNum, BigInteger.ONE);
    RationalFormula r = rmgr.makeVariable("r_big_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(rmgr.equal(r, rmgr.makeNumber(bigRat)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(r)).isEqualTo(bigRat);
      }
    }
  }

  @Test
  public void negativeRationalModelEvaluation() throws SolverException, InterruptedException {
    requireRationals();
    requireModel();

    Rational value = Rational.of(BigInteger.valueOf(-7), BigInteger.valueOf(3));
    RationalFormula r = rmgr.makeVariable("r_neg_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(rmgr.equal(r, rmgr.makeNumber(value)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(r)).isEqualTo(value);
      }
    }
  }

  @Test
  public void largeDenominatorRationalModelEvaluation()
      throws SolverException, InterruptedException {
    requireRationals();
    requireModel();

    Rational value =
        Rational.of(
            new BigInteger("123456789012345678901234567890123456789"),
            new BigInteger("100000000000000000000000000000000000003"));
    RationalFormula r = rmgr.makeVariable("r_large_den_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(rmgr.equal(r, rmgr.makeNumber(value)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(r)).isEqualTo(value);
      }
    }
  }

  @Test
  public void ufCongruenceIsEnforced() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x_uf");
    IntegerFormula y = imgr.makeVariable("y_uf");
    FunctionDeclaration<IntegerFormula> fDecl =
        fmgr.declareUF("f_uf", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula fx = mgr.makeApplication(fDecl, x);
    IntegerFormula fy = mgr.makeApplication(fDecl, y);

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(imgr.equal(x, y));
      prover.push(bmgr.not(imgr.equal(fx, fy)));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

  @Test
  public void modularCongruenceWorks() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula a = imgr.makeNumber(10);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber(0);

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(imgr.modularCongruence(a, b, 5));
      assertThat(prover.isUnsat()).isFalse();
    }

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(bmgr.not(imgr.modularCongruence(a, c, 5)));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

  @Test
  public void floorOnRationalsWorks() throws SolverException, InterruptedException {
    requireRationals();
    requireRationalFloor();

    RationalFormula r = rmgr.makeVariable("r_floor_reg");
    IntegerFormula floor = rmgr.floor(r);

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(
          rmgr.equal(
              r, rmgr.makeNumber(Rational.of(BigInteger.valueOf(7), BigInteger.valueOf(3)))));
      prover.push(imgr.equal(floor, imgr.makeNumber(2)));
      assertThat(prover.isUnsat()).isFalse();
    }

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(
          rmgr.equal(
              r, rmgr.makeNumber(Rational.of(BigInteger.valueOf(-7), BigInteger.valueOf(3)))));
      prover.push(imgr.equal(floor, imgr.makeNumber(-2)));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

  @Test
  public void modelAssignmentsDoNotExposeInternalHelperSymbols()
      throws SolverException, InterruptedException {
    requireRationals();
    requireRationalFloor();
    requireModel();

    RationalFormula r = rmgr.makeVariable("r_visible");
    IntegerFormula floor = rmgr.floor(r);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(
          rmgr.equal(
              r, rmgr.makeNumber(Rational.of(BigInteger.valueOf(7), BigInteger.valueOf(3)))));
      prover.push(imgr.equal(floor, imgr.makeNumber(2)));
      assertThat(prover.isUnsat()).isFalse();

      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(r))
            .isEqualTo(Rational.of(BigInteger.valueOf(7), BigInteger.valueOf(3)));
        assertThat(model.evaluate(floor)).isEqualTo(BigInteger.valueOf(2));
        boolean exposesInternalSymbols =
            model.asList().stream()
                .map(ValueAssignment::getName)
                .anyMatch(name -> name.startsWith("__"));
        assertThat(exposesInternalSymbols).isFalse();
      }
    }
  }

  @Test
  public void bitvectorModelEvaluationIsNotNull() throws SolverException, InterruptedException {
    requireBitvectors();
    requireModel();

    BitvectorFormula bv = bvmgr.makeVariable(32, "bv_model_reg");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bvmgr.equal(bv, bvmgr.makeBitvector(32, 0)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(bv)).isEqualTo(BigInteger.ZERO);
      }
    }
  }

  @Test
  public void signedBitvectorModuloMatchesSmtLibSemantics()
      throws SolverException, InterruptedException {
    requireBitvectors();

    BitvectorFormula ten = bvmgr.makeBitvector(8, 10);
    BitvectorFormula minusTen = bvmgr.makeBitvector(8, -10);
    BitvectorFormula three = bvmgr.makeBitvector(8, 3);
    BitvectorFormula minusThree = bvmgr.makeBitvector(8, -3);
    BitvectorFormula minusTwo = bvmgr.makeBitvector(8, -2);
    BitvectorFormula two = bvmgr.makeBitvector(8, 2);
    BitvectorFormula minusOne = bvmgr.makeBitvector(8, -1);

    assertThatFormula(bvmgr.equal(bvmgr.smodulo(ten, minusThree), minusTwo)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, three), two)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, minusThree), minusOne)).isTautological();
  }

  @Test
  public void intToBitvectorConversionWorksWithSymbolicInput()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireBitvectorToInt();
    requireModel();

    IntegerFormula i = imgr.makeVariable("i_to_bv_reg");
    BitvectorFormula bv = bvmgr.makeBitvector(8, i);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(i, imgr.makeNumber(300)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(bv)).isEqualTo(BigInteger.valueOf(44));
      }
    }
  }

  @Test
  public void signedBitvectorToIntegerModelEvaluationUsesSignedSemantics()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireBitvectorToInt();
    requireIntegers();
    requireModel();

    BitvectorFormula bv = bvmgr.makeVariable(8, "bv_signed_to_int_reg");
    IntegerFormula signed = bvmgr.toIntegerFormula(bv, true);
    IntegerFormula unsigned = bvmgr.toIntegerFormula(bv, false);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bvmgr.equal(bv, bvmgr.makeBitvector(8, 255)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(unsigned)).isEqualTo(BigInteger.valueOf(255));
        assertThat(model.evaluate(signed)).isEqualTo(BigInteger.valueOf(-1));
      }
    }
  }

  @Test
  public void signExtendModelEvaluationUsesSignedExtensionSemantics()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireModel();

    BitvectorFormula x = bvmgr.makeVariable(8, "x_sign_extend_eval_reg");
    BitvectorFormula extended = bvmgr.extend(x, 8, true);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bvmgr.equal(x, bvmgr.makeBitvector(8, 255)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(extended)).isEqualTo(BigInteger.valueOf(65535));
      }
    }
  }

  @Test
  public void indexedRotateModelEvaluationIsSupported()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireModel();

    BitvectorFormula x = bvmgr.makeVariable(8, "x_rotate_indexed_eval_reg");
    BitvectorFormula rotatedLeft = bvmgr.rotateLeft(x, 3);
    BitvectorFormula rotatedRight = bvmgr.rotateRight(x, 2);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bvmgr.equal(x, bvmgr.makeBitvector(8, 1)));
      assertThat(prover.isUnsat()).isFalse();
      try (Model model = prover.getModel()) {
        assertThat(model.evaluate(rotatedLeft)).isEqualTo(BigInteger.valueOf(8));
        assertThat(model.evaluate(rotatedRight)).isEqualTo(BigInteger.valueOf(64));
      }
    }
  }

  @Test
  public void substitutionRebuildSupportsBitvectorBuiltIns()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireBitvectorToInt();
    requireIntegers();

    BitvectorFormula x = bvmgr.makeVariable(8, "x_subst_bv_reg");
    BitvectorFormula y = bvmgr.makeVariable(8, "y_subst_bv_reg");

    BitvectorFormula concat = bvmgr.concat(x, y);
    BitvectorFormula extracted = bvmgr.extract(concat, 7, 0);
    BitvectorFormula extended = bvmgr.extend(y, 8, true);
    BitvectorFormula udiv = bvmgr.divide(x, bvmgr.makeBitvector(8, 3), false);
    BitvectorFormula srem = bvmgr.remainder(x, bvmgr.makeBitvector(8, 5), true);
    BitvectorFormula smod = bvmgr.smodulo(x, bvmgr.makeBitvector(8, 7));
    IntegerFormula signedInt = bvmgr.toIntegerFormula(x, true);
    BitvectorFormula intToBv = bvmgr.makeBitvector(8, signedInt);

    BooleanFormula formula =
        bmgr.and(
            bvmgr.equal(extracted, y),
            bvmgr.equal(extended, bvmgr.extend(y, 8, true)),
            bvmgr.equal(udiv, bvmgr.divide(x, bvmgr.makeBitvector(8, 3), false)),
            bvmgr.equal(srem, bvmgr.remainder(x, bvmgr.makeBitvector(8, 5), true)),
            bvmgr.equal(smod, bvmgr.smodulo(x, bvmgr.makeBitvector(8, 7))),
            imgr.equal(bvmgr.toIntegerFormula(intToBv, false), bvmgr.toIntegerFormula(x, false)));

    BooleanFormula rebuilt = mgr.substitute(formula, ImmutableMap.of());
    assertThatFormula(bmgr.equivalence(formula, rebuilt)).isTautological();
  }
}
