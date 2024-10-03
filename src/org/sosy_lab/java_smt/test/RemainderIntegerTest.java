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

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.*;

public class RemainderIntegerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  ImmutableList<Integer> testValues = ImmutableList.of(-5, -3, -2, -1, 1, 2, 3, 5);

  @Before
  public void init() {
    requireIntegers();
  }

  private int euclideanDivision(int x, int y) {
    int noRemainder = x - euclideanRemainder(x, y);
    return noRemainder / y;
  }

  @Test
  public void integerDivisionTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var i0 = imgr.makeNumber(x);
        var i1 = imgr.makeNumber(y);
        assertWithMessage("divide(%s, %s)", x, y)
            .that(eval(imgr.divide(i0, i1)))
            .isEqualTo(euclideanDivision(x, y));
      }
    }
  }

  private int euclideanRemainder(int x, int y) {
    int mod = x % y;
    if (mod < 0) {
      return mod + Math.abs(y);
    } else {
      return mod;
    }
  }

  @Test
  public void integerModuloTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var i0 = imgr.makeNumber(x);
        var i1 = imgr.makeNumber(y);
        assertWithMessage("modulo(%s, %s)", x, y)
            .that(eval(imgr.modulo(i0, i1)))
            .isEqualTo(euclideanRemainder(x, y));
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
