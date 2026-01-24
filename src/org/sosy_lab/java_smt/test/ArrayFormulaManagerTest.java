// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.api.FormulaType.RationalType;
import static org.sosy_lab.java_smt.api.FormulaType.StringType;
import static org.sosy_lab.java_smt.api.FormulaType.getBitvectorTypeWithSize;
import static org.sosy_lab.java_smt.api.FormulaType.getSinglePrecisionFloatingPointType;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

/** Tests Arrays for all solvers that support it. */
public class ArrayFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void init() {
    requireArrays();
  }

  @Test
  public void testIntIndexIntValue() throws SolverException, InterruptedException {
    requireIntegers();

    // (arr2 = store(arr1, 4, 2)) & !(select(arr2, 4) = 2)
    ArrayFormulaType<IntegerFormula, IntegerFormula> type =
        FormulaType.getArrayType(IntegerType, IntegerType);
    IntegerFormula num2 = imgr.makeNumber(2);
    IntegerFormula num4 = imgr.makeNumber(4);
    ArrayFormula<IntegerFormula, IntegerFormula> arr1 = amgr.makeArray("arr1", type);
    ArrayFormula<IntegerFormula, IntegerFormula> arr2 = amgr.makeArray("arr2", type);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(imgr.equal(num2, amgr.select(arr2, num4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether String Arrays are possible with String indexes
   */
  @Test
  public void testStringIndexStringValue() throws SolverException, InterruptedException {
    requireStrings();

    // (arr2 = store(arr1, "four", "two")) & !(select(arr2, "four") = "two")
    StringFormula num2 = smgr.makeString("two");
    StringFormula num4 = smgr.makeString("four");
    ArrayFormula<StringFormula, StringFormula> arr1 =
        amgr.makeArray("arr1", StringType, StringType);
    ArrayFormula<StringFormula, StringFormula> arr2 =
        amgr.makeArray("arr2", StringType, StringType);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(smgr.equal(num2, amgr.select(arr2, num4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether String Arrays with Int indexes are possible
   */
  @Test
  public void testIntIndexStringValue() throws SolverException, InterruptedException {
    requireStrings();

    // (arr2 = store(arr1, 4, "two")) & !(select(arr2, 4) = "two")
    StringFormula stringTwo = smgr.makeString("two");
    IntegerFormula intFour = imgr.makeNumber(4);
    ArrayFormula<IntegerFormula, StringFormula> arr1 =
        amgr.makeArray("arr1", FormulaType.IntegerType, StringType);
    ArrayFormula<IntegerFormula, StringFormula> arr2 =
        amgr.makeArray("arr2", FormulaType.IntegerType, StringType);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, intFour, stringTwo)),
            bmgr.not(smgr.equal(stringTwo, amgr.select(arr2, intFour))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether String Arrays with bitvector indexes are possible
   */
  @Test
  public void testBvIndexStringValue() throws SolverException, InterruptedException {
    requireStrings();

    // (arr2 = store(arr1, 0100, "two")) & !(select(arr2, 0100) = "two")
    StringFormula stringTwo = smgr.makeString("two");
    BitvectorFormula bv4 = bvmgr.makeBitvector(4, 4);
    ArrayFormula<BitvectorFormula, StringFormula> arr1 =
        amgr.makeArray("arr1", getBitvectorTypeWithSize(4), StringType);
    ArrayFormula<BitvectorFormula, StringFormula> arr2 =
        amgr.makeArray("arr2", getBitvectorTypeWithSize(4), StringType);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, bv4, stringTwo)),
            bmgr.not(smgr.equal(stringTwo, amgr.select(arr2, bv4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether Bitvector Arrays are possible with bv index
   */
  @Test
  public void testBvIndexBvValue() throws SolverException, InterruptedException {
    requireBitvectors();

    // (arr2 = store(arr1, 0100, 0010)) & !(select(arr2, 0100) = 0010)
    BitvectorFormula num2 = bvmgr.makeBitvector(4, 2);
    BitvectorFormula num4 = bvmgr.makeBitvector(4, 4);
    ArrayFormula<BitvectorFormula, BitvectorFormula> arr1 =
        amgr.makeArray("arr1", getBitvectorTypeWithSize(4), getBitvectorTypeWithSize(4));
    ArrayFormula<BitvectorFormula, BitvectorFormula> arr2 =
        amgr.makeArray("arr2", getBitvectorTypeWithSize(4), getBitvectorTypeWithSize(4));
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(bvmgr.equal(num2, amgr.select(arr2, num4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether Rational Arrays are possible with Rational index
   */
  @Test
  public void testRationalIndexRationalValue() throws SolverException, InterruptedException {
    requireRationals();

    // (arr2 = store(arr1, 4, 2)) & !(select(arr2, 4) = 2)
    RationalFormula num2 = rmgr.makeNumber(2);
    RationalFormula num4 = rmgr.makeNumber(4);
    ArrayFormula<RationalFormula, RationalFormula> arr1 =
        amgr.makeArray("arr1", RationalType, RationalType);
    ArrayFormula<RationalFormula, RationalFormula> arr2 =
        amgr.makeArray("arr2", RationalType, RationalType);
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(rmgr.equal(num2, amgr.select(arr2, num4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  /*
   *  Test whether Float Arrays are possible with Float index
   */
  @Test
  public void testFloatIndexFloatValue() throws SolverException, InterruptedException {
    requireFloats();

    // (arr2 = store(arr1, 4.0, 2.0)) & !(select(arr2, 4.0) = 2.0)
    FloatingPointFormula num2 = fpmgr.makeNumber(2, getSinglePrecisionFloatingPointType());
    FloatingPointFormula num4 = fpmgr.makeNumber(4, getSinglePrecisionFloatingPointType());
    ArrayFormula<FloatingPointFormula, FloatingPointFormula> arr1 =
        amgr.makeArray(
            "arr1", getSinglePrecisionFloatingPointType(), getSinglePrecisionFloatingPointType());
    ArrayFormula<FloatingPointFormula, FloatingPointFormula> arr2 =
        amgr.makeArray(
            "arr2", getSinglePrecisionFloatingPointType(), getSinglePrecisionFloatingPointType());
    BooleanFormula query =
        bmgr.and(
            amgr.equivalence(arr2, amgr.store(arr1, num4, num2)),
            bmgr.not(fpmgr.equalWithFPSemantics(num2, amgr.select(arr2, num4))));
    assertThatFormula(query).isUnsatisfiable();
  }

  @Test
  public void testArrayConstWithDefault() throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not yet support array initialization", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);

    for (int elem : new int[] {0, 1, 5, 100, -100}) {
      IntegerFormula defaultElement = imgr.makeNumber(elem);
      IntegerFormula otherElem = imgr.makeNumber(elem + 1);

      ArrayFormula<IntegerFormula, IntegerFormula> arr =
          amgr.makeArray(FormulaType.getArrayType(IntegerType, IntegerType), defaultElement);

      for (int i : new int[] {1, 3, 9, 13}) {
        IntegerFormula index = imgr.makeNumber(i);

        // select(arr, i) == defaultElement, and not otherElem
        assertThatFormula(imgr.equal(defaultElement, amgr.select(arr, index))).isTautological();
        assertThatFormula(imgr.equal(otherElem, amgr.select(arr, index))).isUnsatisfiable();

        // select(store(arr, i, j)) == j, and not defaultElement
        IntegerFormula selectFromStore = amgr.select(amgr.store(arr, index, otherElem), index);
        assertThatFormula(imgr.equal(otherElem, selectFromStore)).isTautological();
        assertThatFormula(imgr.equal(defaultElement, selectFromStore)).isUnsatisfiable();
      }
    }
  }

  @Test
  public void testArrayConstBvWithDefault() throws SolverException, InterruptedException {
    requireBitvectors();
    assume()
        .withMessage("Solver %s does not yet support array initialization", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    final int size = 8;

    for (int elem : new int[] {0, 1, 5, 100, -100}) {
      BitvectorFormula defaultElement = bvmgr.makeBitvector(size, elem);
      BitvectorFormula otherElem = bvmgr.makeBitvector(size, elem + 1);

      BitvectorType bvType = getBitvectorTypeWithSize(size);
      ArrayFormula<BitvectorFormula, BitvectorFormula> arr =
          amgr.makeArray(FormulaType.getArrayType(bvType, bvType), defaultElement);

      for (int i : new int[] {1, 3, 9, 13}) {
        BitvectorFormula index = bvmgr.makeBitvector(size, i);

        // select(arr, i) == defaultElement, and not otherElem
        assertThatFormula(bvmgr.equal(defaultElement, amgr.select(arr, index))).isTautological();
        assertThatFormula(bvmgr.equal(otherElem, amgr.select(arr, index))).isUnsatisfiable();

        // select(store(arr, i, j)) == j, and not defaultElement
        BitvectorFormula selectFromStore = amgr.select(amgr.store(arr, index, otherElem), index);
        assertThatFormula(bvmgr.equal(otherElem, selectFromStore)).isTautological();
        assertThatFormula(bvmgr.equal(defaultElement, selectFromStore)).isUnsatisfiable();
      }
    }
  }

  @Test
  public void testArrayWithManyValues() throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();

    // The example array formula is: for x in [1...N]: arr = store(arr, x, x)
    // as SMTLIB: arr = store(store(store(... store(array, 0, 0), 1, 1), ... , N-1, N-1)
    ArrayFormula<IntegerFormula, IntegerFormula> array =
        amgr.makeArray("array", IntegerType, IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> storedArray = array;
    final int numValues = 100;
    for (int i = 0; i < numValues; i++) {
      storedArray = amgr.store(storedArray, imgr.makeNumber(i), imgr.makeNumber(i));
    }

    // (x >= 0 && x < numValues) => (x == arr[x]) for the defined array
    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula indexAssignment = imgr.equal(x, amgr.select(storedArray, x)); // x == arr[x]
    BooleanFormula query =
        bmgr.implication(
            bmgr.and(
                imgr.greaterOrEquals(x, imgr.makeNumber(0)),
                imgr.lessThan(x, imgr.makeNumber(numValues))),
            indexAssignment);

    assertThatFormula(query).isTautological();
  }
}
