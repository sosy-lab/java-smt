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
import java.util.Random;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.*;

public class RemainderBitvectorEmulatedTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  ImmutableList<Integer> testValues;

  @Before
  public void init() {
    requireBitvectors();
    ImmutableList.Builder<Integer> builder = ImmutableList.builder();
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

  private int euclideanDivision(int x, int y) {
    long noRemainder = x - euclideanRemainder(x, y);
    return (int) (noRemainder / y);
  }

  private int euclideanRemainder(int x, int y) {
    int mod = x % y;
    if (mod < 0) {
      return mod + Math.abs(y);
    } else {
      return mod;
    }
  }

  private int truncatedDivision(int x, int y) {
    int div = euclideanDivision(x, y);
    int mod = truncatedRemainder(x, y);
    if (mod < 0) {
      return div - Integer.signum(x) * Integer.signum(y);
    } else {
      return div;
    }
  }

  @Test
  public void bitvectorDivisionTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var bv0 = bvmgr.makeBitvector(32, x);
        var bv1 = bvmgr.makeBitvector(32, y);
        assertWithMessage("divide(%s, %s)", x, y)
            .that(eval(bvmgr.divide(bv0, bv1, true)))
            .isEqualTo(truncatedDivision(x, y));
      }
    }
  }

  private int truncatedRemainder(int x, int y) {
    int mod = euclideanRemainder(x, y);
    if (x < 0 && mod > 0) {
      return mod - Math.abs(y);
    } else {
      return mod;
    }
  }

  @Test
  public void bitvectorRemainderTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var bv0 = bvmgr.makeBitvector(32, x);
        var bv1 = bvmgr.makeBitvector(32, y);
        assertWithMessage("remainder(%s, %s)", x, y)
            .that(eval(bvmgr.remainder(bv0, bv1, true)))
            .isEqualTo(truncatedRemainder(x, y));
      }
    }
  }

  private int floorRemainder(int x, int y) {
    int mod = euclideanRemainder(x, y);
    if (y < 0 && mod > 0) {
      return mod - Math.abs(y);
    } else {
      return mod;
    }
  }

  @Test
  public void bitvectorModuloTest() {
    for (int x : testValues) {
      for (int y : testValues) {
        var bv0 = bvmgr.makeBitvector(32, x);
        var bv1 = bvmgr.makeBitvector(32, y);
        assertWithMessage("smodulo(%s, %s)", x, y)
            .that(eval(bvmgr.smodulo(bv0, bv1)))
            .isEqualTo(floorRemainder(x, y));
      }
    }
  }

  public int eval(BitvectorFormula pFormula) {
    BitvectorFormula var = bvmgr.makeVariable(32, "v");
    try (ProverEnvironment prover =
        context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.push(bvmgr.equal(var, pFormula));
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
