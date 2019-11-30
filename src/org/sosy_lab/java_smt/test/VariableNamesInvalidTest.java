/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@RunWith(Parameterized.class)
@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesInvalidTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  // currently the only invalid String is the empty String

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBoolVariable() {
    @SuppressWarnings("unused")
    Formula var = bmgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidIntVariable() {
    requireIntegers();
    @SuppressWarnings("unused")
    Formula var = imgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidRatVariable() {
    requireRationals();
    @SuppressWarnings("unused")
    Formula var = rmgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBVVariable() {
    requireBitvectors();
    @SuppressWarnings("unused")
    Formula var = bvmgr.makeVariable(4, "");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidFloatVariable() {
    requireFloats();
    @SuppressWarnings("unused")
    Formula var = fpmgr.makeVariable("", FormulaType.getSinglePrecisionFloatingPointType());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidIntArrayVariable() {
    requireIntegers();
    requireArrays();
    @SuppressWarnings("unused")
    Formula var = amgr.makeArray("", FormulaType.IntegerType, FormulaType.IntegerType);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBvArrayVariable() {
    requireBitvectors();
    requireArrays();
    @SuppressWarnings("unused")
    Formula var =
        amgr.makeArray(
            "", FormulaType.getBitvectorTypeWithSize(2), FormulaType.getBitvectorTypeWithSize(2));
  }
}
