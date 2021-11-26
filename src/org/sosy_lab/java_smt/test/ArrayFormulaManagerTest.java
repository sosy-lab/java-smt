// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.api.FormulaType.StringType;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
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
}
