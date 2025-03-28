// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
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
public class BitvectorFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private static final BitvectorType bvType4 = FormulaType.getBitvectorTypeWithSize(4);

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

  @Test
  public void bvTooLargeNum() {
    // value 4 is too large for size 2
    assertThrows(IllegalArgumentException.class, () -> bvmgr.makeBitvector(2, 4));
    if (solver != Solvers.BOOLECTOR) {
      // value 2 is too large for size 1
      assertThrows(IllegalArgumentException.class, () -> bvmgr.makeBitvector(1, 2));
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvLargeNum() {
    bvmgr.makeBitvector(2, 3); // value 3 should be possible for size 2
    if (solver != Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(1, 1); // value 1 should be possible for size 1
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvSmallNum() {
    bvmgr.makeBitvector(2, -1); // value -1 should be possible for size 2
    if (solver != Solvers.BOOLECTOR) {
      bvmgr.makeBitvector(1, -1); // value -1 should be possible for size 1
    }
  }

  @Test
  public void bvTooSmallNum() {
    // value -4 is too small for size 2
    assertThrows(IllegalArgumentException.class, () -> bvmgr.makeBitvector(2, -4));
    if (solver != Solvers.BOOLECTOR) {
      // value -2 is too small for size 1
      assertThrows(IllegalArgumentException.class, () -> bvmgr.makeBitvector(1, -2));
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
      for (int i : new int[] {-max / 2, max - 1, 0}) {
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
      new int[] {0, 1, 3, 4, 8, 32, 100, 512, 100000, Integer.MAX_VALUE};

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

    for (int size : new int[] {1, 2, 4}) {
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

  @Test
  public void bvExtractTooLargeNumEndSigned() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, 5, 0));
  }

  @Test
  public void bvExtractTooLargeNumStartSigned() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, 4, 5));
  }

  @Test
  public void bvExtractTooLargeNumStartAltSigned() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, 3, 4));
  }

  @Test
  public void bvExtractNegNumEnd() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, -1, 0));
  }

  @Test
  public void bvExtractNegNumStart() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, 1, -1));
  }

  @Test
  public void bvExtractNegNumStartEnd() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extract(bv, -1, -1));
  }

  @Test
  public void bvExtendNegNum() {
    // Use bv > 1 because of Boolector
    BitvectorFormula bv = bvmgr.makeBitvector(4, 4);
    assertThrows(IllegalArgumentException.class, () -> bvmgr.extend(bv, -1, true));
  }

  @Test
  public void bvIntArray() {
    requireArrays();
    assume()
        .withMessage("Solver %s does not support arrays with integer index", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.BOOLECTOR, Solvers.BITWUZLA);

    BitvectorFormula bv = bvmgr.makeBitvector(4, 3);
    ArrayFormula<IntegerFormula, BitvectorFormula> arr =
        amgr.makeArray("arr", FormulaType.IntegerType, bvType4);
    IntegerFormula index = imgr.makeNumber(12);
    arr = amgr.store(arr, index, bv);

    assertThat(mgr.getFormulaType(arr))
        .isEqualTo(FormulaType.getArrayType(FormulaType.IntegerType, bvType4));
  }

  @Test
  public void bvBvArray() {
    requireArrays();

    BitvectorFormula bv = bvmgr.makeBitvector(4, 3);
    ArrayFormula<BitvectorFormula, BitvectorFormula> arr = amgr.makeArray("arr", bvType4, bvType4);
    BitvectorFormula index = bvmgr.makeBitvector(4, 2);
    arr = amgr.store(arr, index, bv);

    assertThat(mgr.getFormulaType(arr)).isEqualTo(FormulaType.getArrayType(bvType4, bvType4));
  }

  @Test
  public void bvDistinct() throws SolverException, InterruptedException {
    for (int bitsize : new int[] {2, 4, 6}) {
      if (solverToUse() == Solvers.CVC5 && bitsize > 4) {
        // CVC5 runs endlessly for > 4; A issue is open for this as CVC4 can solve this in less than
        // a second. See: https://github.com/cvc5/cvc5/discussions/8361
        break;
      }
      List<BitvectorFormula> bvs = new ArrayList<>();
      for (int i = 0; i < 1 << bitsize; i++) {
        bvs.add(bvmgr.makeVariable(bitsize, "a" + i + "_" + bitsize));
      }
      assertThatFormula(bvmgr.distinct(bvs.subList(0, 1 << (bitsize - 1)))).isSatisfiable();
      assertThatFormula(bvmgr.distinct(bvs)).isSatisfiable();
      bvs.add(bvmgr.makeVariable(bitsize, "b" + "_" + bitsize));
      assertThatFormula(bvmgr.distinct(bvs)).isUnsatisfiable();
    }
  }

  @Test
  public void bvVarDistinct() throws SolverException, InterruptedException {
    BitvectorFormula a = bvmgr.makeVariable(4, "a");
    BitvectorFormula num3 = bvmgr.makeBitvector(4, 3);

    assertThatFormula(bvmgr.distinct(List.of(a, num3))).isSatisfiable();
    assertThatFormula(bvmgr.distinct(List.of(a, a))).isUnsatisfiable();
    assertThatFormula(bvmgr.distinct(List.of(num3, num3))).isUnsatisfiable();
  }

  @Test
  public void bvIsZeroAfterShiftLeft() throws SolverException, InterruptedException {
    BitvectorFormula one = bvmgr.makeBitvector(32, 1);

    // unsigned char
    BitvectorFormula a = bvmgr.makeVariable(8, "char_a");
    BitvectorFormula b = bvmgr.makeVariable(8, "char_b");
    BitvectorFormula rightOp = bvmgr.makeBitvector(32, 7);

    // 'cast' a to unsigned int
    a = bvmgr.extend(a, 32 - 8, false);
    b = bvmgr.extend(b, 32 - 8, false);
    a = bvmgr.or(a, one);
    b = bvmgr.or(b, one);
    a = bvmgr.extract(a, 7, 0);
    b = bvmgr.extract(b, 7, 0);
    a = bvmgr.extend(a, 32 - 8, false);
    b = bvmgr.extend(b, 32 - 8, false);

    a = bvmgr.shiftLeft(a, rightOp);
    b = bvmgr.shiftLeft(b, rightOp);
    a = bvmgr.extract(a, 7, 0);
    b = bvmgr.extract(b, 7, 0);
    BooleanFormula f = bmgr.not(bvmgr.equal(a, b));

    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void bvRotateByConstant() throws SolverException, InterruptedException {
    for (int bitsize : new int[] {8, 13, 25, 31}) {
      BitvectorFormula zero = bvmgr.makeBitvector(bitsize, 0);
      BitvectorFormula a = bvmgr.makeVariable(bitsize, "a" + bitsize);
      BitvectorFormula b = bvmgr.makeVariable(bitsize, "b" + bitsize);
      BitvectorFormula zeroA = bvmgr.concat(zero, a);
      BitvectorFormula bZero = bvmgr.concat(b, zero);

      // shift is small enough to be in range of the bitsize.
      BitvectorFormula shift = bvmgr.makeBitvector(bitsize * 2, bitsize);

      // rotating left and right is identity
      assertThatFormula(bvmgr.equal(a, bvmgr.rotateLeft(bvmgr.rotateRight(a, 7), 7)))
          .isTautological();
      assertThatFormula(bvmgr.equal(a, bvmgr.rotateRight(bvmgr.rotateLeft(a, 7), 7)))
          .isTautological();

      // rotating twice by half is identity
      assertThatFormula(
              bvmgr.equal(zeroA, bvmgr.rotateLeft(bvmgr.rotateLeft(zeroA, bitsize), bitsize)))
          .isTautological();
      assertThatFormula(
              bvmgr.equal(bZero, bvmgr.rotateRight(bvmgr.rotateRight(bZero, bitsize), bitsize)))
          .isTautological();

      // rotating a half-zero variable is shifting
      assertThatFormula(
              bvmgr.equal(bvmgr.rotateLeft(zeroA, bitsize), bvmgr.shiftLeft(zeroA, shift)))
          .isTautological();
      assertThatFormula(
              bvmgr.equal(bvmgr.rotateRight(bZero, bitsize), bvmgr.shiftRight(bZero, shift, false)))
          .isTautological();
    }
  }

  @Test
  public void bvRotateByBV() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver is too slow for this test")
        .that(solver)
        .isNoneOf(Solvers.PRINCESS, Solvers.SMTINTERPOL);

    for (int bitsize : new int[] {8, 13, 25, 31}) {
      BitvectorFormula zero = bvmgr.makeBitvector(bitsize, 0);
      BitvectorFormula a = bvmgr.makeVariable(bitsize, "a" + bitsize);
      BitvectorFormula b = bvmgr.makeVariable(bitsize, "b" + bitsize);
      BitvectorFormula zeroA = bvmgr.concat(zero, a);
      BitvectorFormula bZero = bvmgr.concat(b, zero);

      // shift is small enough to be in range of the bitsize.
      BitvectorFormula shift = bvmgr.makeBitvector(bitsize * 2, bitsize);

      // rotating left and right is identity
      assertThatFormula(bvmgr.equal(a, bvmgr.rotateLeft(bvmgr.rotateRight(a, b), b)))
          .isTautological();
      assertThatFormula(bvmgr.equal(a, bvmgr.rotateRight(bvmgr.rotateLeft(a, b), b)))
          .isTautological();

      // rotating twice by half is identity
      assertThatFormula(bvmgr.equal(zeroA, bvmgr.rotateLeft(bvmgr.rotateLeft(zeroA, shift), shift)))
          .isTautological();
      assertThatFormula(
              bvmgr.equal(bZero, bvmgr.rotateRight(bvmgr.rotateRight(bZero, shift), shift)))
          .isTautological();

      // rotating a half-zero variable is shifting
      assertThatFormula(bvmgr.equal(bvmgr.rotateLeft(zeroA, shift), bvmgr.shiftLeft(zeroA, shift)))
          .isTautological();
      assertThatFormula(
              bvmgr.equal(bvmgr.rotateRight(bZero, shift), bvmgr.shiftRight(bZero, shift, false)))
          .isTautological();
    }
  }

  @Test
  public void bvIsIdenticalAfterFullRotation() throws SolverException, InterruptedException {
    assume()
        .withMessage("SMTInterpol is too slow for this test")
        .that(solver)
        .isNotEqualTo(Solvers.SMTINTERPOL);

    for (int bitsize : new int[] {2, 4, 8, 16, 32, 55}) {
      BitvectorFormula number = bvmgr.makeVariable(bitsize, "NUM_ROT_" + bitsize);
      for (int multiplier : new int[] {0, 1, 2, 5, 17, 37, 111, 1111}) {
        int toRotate = multiplier * bitsize;
        if (toRotate >= (1 << bitsize)) {
          continue; // ignore numbers larger than bitsize
        }
        BitvectorFormula rot = bvmgr.makeBitvector(bitsize, toRotate);
        assertThatFormula(bvmgr.equal(number, bvmgr.rotateLeft(number, rot))).isTautological();
        assertThatFormula(bvmgr.equal(number, bvmgr.rotateRight(number, rot))).isTautological();
      }
    }
  }

  @Test
  public void bvInRange() throws SolverException, InterruptedException {
    requireBitvectors();

    assertThatFormula(
            bvmgr.equal(
                bvmgr.add(bvmgr.makeBitvector(4, 15), bvmgr.makeBitvector(4, -8)),
                bvmgr.makeBitvector(4, 7)))
        .isTautological();
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvOutOfRange() {
    for (int[] sizeAndValue : new int[][] {{4, 32}, {4, -9}, {8, 300}, {8, -160}}) {
      assertThrows(
          IllegalArgumentException.class,
          () -> bvmgr.makeBitvector(sizeAndValue[0], sizeAndValue[1]));
    }

    for (int size : new int[] {4, 6, 8, 10, 16, 32}) {
      // allowed values
      bvmgr.makeBitvector(size, (1L << size) - 1);
      bvmgr.makeBitvector(size, -(1L << (size - 1)));

      // forbitten values
      assertThrows(IllegalArgumentException.class, () -> bvmgr.makeBitvector(size, 1L << size));
      assertThrows(
          IllegalArgumentException.class, () -> bvmgr.makeBitvector(size, -(1L << (size - 1)) - 1));
    }

    for (int size : new int[] {36, 40, 64, 65, 100, 128, 200, 250, 1000, 10000}) {
      if (size > 64) {
        assume()
            .withMessage("Solver does not support large bitvectors")
            .that(solverToUse())
            .isNotEqualTo(Solvers.CVC4);
      }

      // allowed values
      bvmgr.makeBitvector(size, BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE));
      bvmgr.makeBitvector(size, BigInteger.ONE.shiftLeft(size - 1).negate());

      // forbitten values
      assertThrows(
          IllegalArgumentException.class,
          () -> bvmgr.makeBitvector(size, BigInteger.ONE.shiftLeft(size)));
      assertThrows(
          IllegalArgumentException.class,
          () ->
              bvmgr.makeBitvector(
                  size, BigInteger.ONE.shiftLeft(size - 1).negate().subtract(BigInteger.ONE)));
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvITETest() {
    BitvectorType bv8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorFormula x = bvmgr.makeVariable(bv8, "x");
    bmgr.ifThenElse(bmgr.makeBoolean(true), x, x);
  }

  @Test
  public void bvModulo() throws SolverException, InterruptedException {
    // FIXME Returns "unknown" for the negative cases
    assume().that(solver).isNotEqualTo(Solvers.SMTINTERPOL);

    BitvectorFormula ten = bvmgr.makeBitvector(8, 10);
    BitvectorFormula five = bvmgr.makeBitvector(8, 5);
    BitvectorFormula three = bvmgr.makeBitvector(8, 3);
    BitvectorFormula two = bvmgr.makeBitvector(8, 2);
    BitvectorFormula one = bvmgr.makeBitvector(8, 1);
    BitvectorFormula zero = bvmgr.makeBitvector(8, 0);
    BitvectorFormula minusTen = bvmgr.makeBitvector(8, -10);
    BitvectorFormula minusThree = bvmgr.makeBitvector(8, -3);
    BitvectorFormula minusTwo = bvmgr.makeBitvector(8, -2);
    BitvectorFormula minusOne = bvmgr.makeBitvector(8, -1);

    assertThatFormula(bvmgr.equal(bvmgr.smodulo(ten, five), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(ten, three), one)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(ten, minusThree), minusTwo)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, five), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, three), two)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, minusThree), minusOne)).isTautological();
  }

  @Test
  public void bvModuloByZero() throws SolverException, InterruptedException {
    BitvectorFormula ten = bvmgr.makeBitvector(8, 10);
    BitvectorFormula zero = bvmgr.makeBitvector(8, 0);
    BitvectorFormula minusTen = bvmgr.makeBitvector(8, -10);

    assertThatFormula(bvmgr.equal(bvmgr.smodulo(zero, zero), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(ten, zero), ten)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.smodulo(minusTen, zero), minusTen)).isTautological();
  }

  @Test
  public void bvRemainder() throws SolverException, InterruptedException {
    BitvectorFormula ten = bvmgr.makeBitvector(8, 10);
    BitvectorFormula five = bvmgr.makeBitvector(8, 5);
    BitvectorFormula three = bvmgr.makeBitvector(8, 3);
    BitvectorFormula one = bvmgr.makeBitvector(8, 1);
    BitvectorFormula zero = bvmgr.makeBitvector(8, 0);
    BitvectorFormula minusTen = bvmgr.makeBitvector(8, -10);
    BitvectorFormula minusThree = bvmgr.makeBitvector(8, -3);
    BitvectorFormula minusOne = bvmgr.makeBitvector(8, -1);

    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, five, true), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, three, true), one)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, minusThree, true), one)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, five, true), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, three, true), minusOne))
        .isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, minusThree, true), minusOne))
        .isTautological();

    // in unsigned context, signed negative numbers are actually huge positive numbers.
    // feel free to compute them by hand :-)
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, five, false), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, three, false), one)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, minusThree, false), ten)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, five, false), one)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, three, false), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, minusThree, false), minusTen))
        .isTautological();
  }

  @Test
  public void bvRemainderByZero() throws SolverException, InterruptedException {
    BitvectorFormula ten = bvmgr.makeBitvector(8, 10);
    BitvectorFormula zero = bvmgr.makeBitvector(8, 0);
    BitvectorFormula minusTen = bvmgr.makeBitvector(8, -10);

    assertThatFormula(bvmgr.equal(bvmgr.remainder(zero, zero, true), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, zero, true), ten)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, zero, true), minusTen))
        .isTautological();

    assertThatFormula(bvmgr.equal(bvmgr.remainder(zero, zero, false), zero)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(ten, zero, false), ten)).isTautological();
    assertThatFormula(bvmgr.equal(bvmgr.remainder(minusTen, zero, false), minusTen))
        .isTautological();
  }
}
