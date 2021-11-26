// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.api.FormulaType.RationalType;
import static org.sosy_lab.java_smt.api.FormulaType.StringType;
import static org.sosy_lab.java_smt.api.FormulaType.getBitvectorTypeWithSize;
import static org.sosy_lab.java_smt.api.FormulaType.getSinglePrecisionFloatingPointType;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

/** Tests Arrays for all solvers that support it. */
@RunWith(Parameterized.class)
public class ArrayFormulaManagerTest extends SolverBasedTest0 {

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
    requireArrays();
  }

  @Test
  public void uniqueType() throws SolverException, InterruptedException {
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
   *  Test whether or not String Arrays are possible
   */
  @Test
  public void basicStringTypeTest() throws SolverException, InterruptedException {
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
   *  Test whether or not Bitvector Arrays are possible
   */
  @Test
  public void basicBitvectorTypeTest() throws SolverException, InterruptedException {
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
   *  Test whether or not Rational Arrays are possible
   */
  @Test
  public void basicRationalTypeTest() throws SolverException, InterruptedException {
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
   *  Test whether or not Float Arrays are possible
   */
  @Test
  public void basicFloatTypeTest() throws SolverException, InterruptedException {
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
}
