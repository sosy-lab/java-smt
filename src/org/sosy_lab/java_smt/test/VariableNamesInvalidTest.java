// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.junit.Assert.assertThrows;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import org.junit.Test;
import org.sosy_lab.java_smt.api.FormulaType;

@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesInvalidTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // currently the only invalid String is the empty String

  @Test
  public void testInvalidBoolVariable() {
    assertThrows(IllegalArgumentException.class, () -> bmgr.makeVariable(""));
  }

  @Test
  public void testInvalidIntVariable() {
    requireIntegers();
    assertThrows(IllegalArgumentException.class, () -> imgr.makeVariable(""));
  }

  @Test
  public void testInvalidRatVariable() {
    requireRationals();
    assertThrows(IllegalArgumentException.class, () -> rmgr.makeVariable(""));
  }

  @Test
  public void testInvalidBVVariable() {
    requireBitvectors();
    assertThrows(IllegalArgumentException.class, () -> bvmgr.makeVariable(4, ""));
  }

  @Test
  public void testInvalidFloatVariable() {
    requireFloats();
    assertThrows(
        IllegalArgumentException.class,
        () -> fpmgr.makeVariable("", FormulaType.getSinglePrecisionFloatingPointType()));
  }

  @Test
  public void testInvalidIntArrayVariable() {
    requireIntegers();
    requireArrays();
    assertThrows(
        IllegalArgumentException.class,
        () -> amgr.makeArray("", FormulaType.IntegerType, FormulaType.IntegerType));
  }

  @Test
  public void testInvalidBvArrayVariable() {
    requireBitvectors();
    requireArrays();
    assertThrows(
        IllegalArgumentException.class,
        () ->
            amgr.makeArray(
                "",
                FormulaType.getBitvectorTypeWithSize(2),
                FormulaType.getBitvectorTypeWithSize(2)));
  }
}
