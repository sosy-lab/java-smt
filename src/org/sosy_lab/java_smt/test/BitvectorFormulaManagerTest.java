/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Tests bitvectors for all solvers that support it. Notice: Boolector does not support integer
 * theory or bitvectors length 1.
 */
@RunWith(Parameterized.class)
public class BitvectorFormulaManagerTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Before
  public void init() {
    requireBitvectors();
  }

  @Test
  public void bvType() {
    int[] testValues;
    if (solver == Solvers.BOOLECTOR) {
      testValues = new int[] {2, 4, 32, 64, 1000};
    } else {
      testValues = new int[] {1, 2, 4, 32, 64, 1000};
    }
    for (int i : testValues) {
      BitvectorType type = FormulaType.getBitvectorTypeWithSize(i);
      assertWithMessage("bitvector type size").that(type.getSize()).isEqualTo(i);
      BitvectorFormula var = bvmgr.makeVariable(type, "x" + i);
      BitvectorType result = (BitvectorType) mgr.getFormulaType(var);
      assertWithMessage("bitvector size").that(result.getSize()).isEqualTo(i);
    }
  }

  @Test
  public void bvOne() throws SolverException, InterruptedException {
    int[] testValues;
    if (solver == Solvers.BOOLECTOR) {
      testValues = new int[] {2, 4, 32, 64, 1000};
    } else {
      testValues = new int[] {1, 2, 4, 32, 64, 1000};
    }
    for (int i : testValues) {
      BitvectorFormula var = bvmgr.makeVariable(i, "x" + i);
      BitvectorFormula num0 = bvmgr.makeBitvector(i, 0);
      BitvectorFormula num1 = bvmgr.makeBitvector(i, 1);
      assertThatFormula(bvmgr.equal(var, num0)).isSatisfiable();
      assertThatFormula(bvmgr.equal(var, num1)).isSatisfiable();
    }
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public void bvTooLargeNum() {
    if (solver == Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(2, 4); // value 4 is too large for size 2
    } else {
      bvmgr.makeBitvector(1, 2); // value 2 is too large for size 1
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvLargeNum() {
    if (solver == Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(2, 3); // value 3 should be possible for size 2
    } else {
      bvmgr.makeBitvector(1, 1); // value 1 should be possible for size 1
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvSmallNum() {
    if (solver == Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(2, -1); // value -1 should be possible for size 2
    } else {
      bvmgr.makeBitvector(1, -1); // value -1 should be possible for size 1
    }
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public void bvTooSmallNum() {
    if (solver == Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(2, -4); // value -4 is too small for size 2
    } else {
      bvmgr.makeBitvector(1, -2); // value -2 is too small for size 1
    }
  }

  @Test
  public void bvModelValue32bit() throws SolverException, InterruptedException {
    BitvectorFormula var = bvmgr.makeVariable(32, "var");

    Map<Long, Long> values = new LinkedHashMap<>();
    long int32 = 1L << 32;

    // positive signed values stay equal
    values.put(0L, 0L);
    values.put(1L, 1L);
    values.put(2L, 2L);
    values.put(123L, 123L);
    values.put((long) Integer.MAX_VALUE, (long) Integer.MAX_VALUE);

    // positive unsigned values stay equal
    values.put(Integer.MAX_VALUE + 1L, Integer.MAX_VALUE + 1L);
    values.put(Integer.MAX_VALUE + 2L, Integer.MAX_VALUE + 2L);
    values.put(Integer.MAX_VALUE + 123L, Integer.MAX_VALUE + 123L);
    values.put(int32 - 1L, int32 - 1);
    values.put(int32 - 2L, int32 - 2);
    values.put(int32 - 123L, int32 - 123);

    // negative signed values are converted to unsigned
    values.put(-1L, int32 - 1);
    values.put(-2L, int32 - 2);
    values.put(-123L, int32 - 123);
    values.put((long) Integer.MIN_VALUE, 1L + Integer.MAX_VALUE);

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            ProverOptions.GENERATE_MODELS, ProverOptions.GENERATE_UNSAT_CORE)) {
      for (Map.Entry<Long, Long> entry : values.entrySet()) {
        prover.push(bvmgr.equal(var, bvmgr.makeBitvector(32, entry.getKey())));
        assertThat(prover).isSatisfiable();
        try (Model model = prover.getModel()) {
          Object value = model.evaluate(var);
          assertThat(value).isEqualTo(BigInteger.valueOf(entry.getValue()));
        }
        prover.pop();
      }
    }
  }

  @Test
  public void bvToInt() throws SolverException, InterruptedException {
    requireBitvectorToInt();
    requireIntegers();

    for (int size : new int[] {1, 2, 4, 8}) {
      int max = 1 << size;
      // number is in range of bitsize
      for (int i = -max / 2; i < max; i++) {
        BitvectorFormula bv = bvmgr.makeBitvector(size, i);
        IntegerFormula num = imgr.makeNumber(i);
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, num))).isTautological();
        IntegerFormula nSigned = bvmgr.toIntegerFormula(bv, true);
        IntegerFormula nUnsigned = bvmgr.toIntegerFormula(bv, false);
        if (i < max / 2) {
          assertThatFormula(imgr.equal(num, nSigned)).isTautological();
          assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, nSigned))).isTautological();
        }
        if (i >= 0) {
          assertThatFormula(imgr.equal(num, nUnsigned)).isTautological();
          assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, nUnsigned))).isTautological();
        }
      }
    }
  }

  @Test
  public void bvToIntEquality() throws SolverException, InterruptedException {
    requireBitvectorToInt();
    requireIntegers();

    for (int size : new int[] {10, 16, 20, 32, 64}) {
      for (int i : new int[] {1, 2, 4, 32, 64, 100}) {
        // number is in range of bitsize
        BitvectorFormula bv = bvmgr.makeBitvector(size, i);
        IntegerFormula num = imgr.makeNumber(i);
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, num))).isTautological();
        IntegerFormula nSigned = bvmgr.toIntegerFormula(bv, true);
        IntegerFormula nUnsigned = bvmgr.toIntegerFormula(bv, false);
        assertThatFormula(imgr.equal(num, nSigned)).isTautological();
        assertThatFormula(imgr.equal(num, nUnsigned)).isTautological();
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, nSigned))).isTautological();
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, nUnsigned))).isTautological();
      }
    }
  }

  private static final int[] SOME_SIZES = new int[] {1, 2, 4, 10, 16, 20, 32, 60};
  private static final int[] SOME_NUMBERS =
      new int[] {
        0, 1, 2, 3, 4, 5, 6, 7, 8, 32, 64, 100, 150, 512, 1024, 100000, 1000000, Integer.MAX_VALUE,
      };

  @Test
  public void bvToIntEqualityWithOverflow() throws SolverException, InterruptedException {
    requireBitvectorToInt();
    requireIntegers();

    for (int size : SOME_SIZES) {
      for (int i : SOME_NUMBERS) {
        // number might be larger than range of bitsize
        long upperBound = 1L << size;
        long iMod = i % upperBound;
        IntegerFormula num = imgr.makeNumber(i);
        IntegerFormula nUnsigned = imgr.makeNumber(iMod);
        IntegerFormula nSigned = imgr.makeNumber(iMod < upperBound / 2 ? iMod : iMod - upperBound);
        BitvectorFormula bv = bvmgr.makeBitvector(size, iMod);
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, num))).isTautological();
        assertThat(mgr.getFormulaType(bvmgr.toIntegerFormula(bv, true)))
            .isEqualTo(FormulaType.IntegerType);
        assertThatFormula(imgr.equal(nSigned, bvmgr.toIntegerFormula(bv, true))).isTautological();
        assertThatFormula(imgr.equal(nUnsigned, bvmgr.toIntegerFormula(bv, false)))
            .isTautological();
      }
    }
  }

  @Test
  public void bvToIntEqualityWithOverflowNegative() throws SolverException, InterruptedException {
    requireBitvectorToInt();
    requireIntegers();

    for (int size : SOME_SIZES) {
      for (int i : SOME_NUMBERS) {
        // make number negative
        int negI = -i;
        // number might be larger than range of bitsize
        long upperBound = 1L << size;
        long iMod = negI % upperBound;
        IntegerFormula num = imgr.makeNumber(negI);
        IntegerFormula nUnsigned = imgr.makeNumber(iMod >= 0 ? iMod : iMod + upperBound);
        IntegerFormula nSigned = imgr.makeNumber(iMod < -upperBound / 2 ? iMod + upperBound : iMod);
        BitvectorFormula bv =
            bvmgr.makeBitvector(size, iMod >= -upperBound / 2 ? iMod : iMod + upperBound);
        assertThatFormula(bvmgr.equal(bv, bvmgr.makeBitvector(size, num))).isTautological();
        assertThatFormula(imgr.equal(nSigned, bvmgr.toIntegerFormula(bv, true))).isTautological();
        assertThatFormula(imgr.equal(nUnsigned, bvmgr.toIntegerFormula(bv, false)))
            .isTautological();
      }
    }
  }

  @Test
  public void bvToIntEqualityWithSymbols() throws SolverException, InterruptedException {
    requireBitvectorToInt();
    requireIntegers();

    for (int size : new int[] {1, 2, 4, 8}) {
      IntegerFormula var = imgr.makeVariable("x_" + size);

      // x == int(bv(x)) is sat for small values
      assertThatFormula(
              imgr.equal(var, bvmgr.toIntegerFormula(bvmgr.makeBitvector(size, var), true)))
          .isSatisfiable();

      // x == int(bv(x)) is unsat for large values
      assertThatFormula(
              bmgr.not(
                  imgr.equal(var, bvmgr.toIntegerFormula(bvmgr.makeBitvector(size, var), true))))
          .isSatisfiable();

      BitvectorFormula bvar = bvmgr.makeVariable(size, "y_" + size);

      // y == bv(int(y)) is sat for all values
      assertThatFormula(
              bvmgr.equal(bvar, bvmgr.makeBitvector(size, bvmgr.toIntegerFormula(bvar, true))))
          .isTautological();
    }
  }
}
