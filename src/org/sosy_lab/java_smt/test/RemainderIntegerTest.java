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

import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.Random;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Test the behavior of integer division and modulo in JavaSMT and compare it to the same operations
 * in Java.
 */
public class RemainderIntegerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  ImmutableList<Integer> testValues;

  @Before
  public void init() {
    requireIntegers();
    ImmutableList.Builder<Integer> builder = ImmutableList.builder();
    builder.add(0);
    builder.add(1);
    builder.add(Integer.MIN_VALUE);
    Random random = new Random(0);
    int c = 0;
    while (c < 20) {
      int r = random.nextInt();
      if (r != 0) {
        builder.add(r);
        c++;
      }
    }
    testValues = builder.build();
  }

  /**
   * Euclidean division.
   *
   * <p>In Euclidean division the remainder is always positive and the quotient needs to be rounded
   * accordingly.
   *
   * <p>More formally, when dividing <code>a</code> by <code>b</code> we have <code>a = k*b + r
   * </code> where <code> k</code> is the quotient <code>a/b</code> and <code>r</code> is the
   * remainder of the division. In Euclidean division we now requires <code>0 <= r < b</code> to
   * hold, which uniquely determines the equation.
   */
  static int euclideanDivision(int x, int y) {
    int div = x / y;
    if (x < 0 && x != y * div) {
      return div - Integer.signum(y);
    } else {
      return div;
    }
  }

  /**
   * Test Integer division.
   *
   * <p>JavaSMT uses {@link #euclideanDivision(int, int) Euclidean division} for integer formulas.
   */
  @Test
  public void integerDivisionTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var i0 = imgr.makeNumber(x);
        var i1 = imgr.makeNumber(y);
        if (y != 0) {
          assertWithMessage("divide(%s, %s)", x, y)
              .that(eval(imgr.divide(i0, i1)))
              .isEqualTo(euclideanDivision(x, y));
        }
      }
    }
  }

  /**
   * Euclidean remainder.
   *
   * <p>See {@link #euclideanDivision(int, int)} for the definition.
   */
  static int euclideanRemainder(int x, int y) {
    int mod = x % y;
    if (mod < 0) {
      return mod + Math.abs(y);
    } else {
      return mod;
    }
  }

  /**
   * Test Integer modulo.
   *
   * <p>JavaSMT uses the {@link #euclideanRemainder(int, int) Euclidean remainder} for integer
   * formulas.
   */
  @Test
  public void integerModuloTest() {
    // Mathsat does not support modulo for integer formulas
    assume().that(solverToUse()).isNotEqualTo(SolverContextFactory.Solvers.MATHSAT5);
    for (int x : testValues) {
      for (int y : testValues) {
        var i0 = imgr.makeNumber(x);
        var i1 = imgr.makeNumber(y);
        if (y != 0) {
          assertWithMessage("modulo(%s, %s)", x, y)
              .that(eval(imgr.modulo(i0, i1)))
              .isEqualTo(euclideanRemainder(x, y));
        }
      }
    }
  }

  public int eval(NumeralFormula.IntegerFormula pFormula) {
    NumeralFormula.IntegerFormula var = imgr.makeVariable("v");
    try (ProverEnvironment prover =
        context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(var, pFormula));
      Preconditions.checkArgument(!prover.isUnsat());
      try (Model model = prover.getModel()) {
        return model.evaluate(var).intValue();
      }
    } catch (InterruptedException e) {
      return 0;
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }
  }
}
