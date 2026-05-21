// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

public class SolverFormulaTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // TODO: UFs exclusively with constants/empty and a separate test that includes variables
  // TODO: a test that the shared constants are also usable and return the correct results for
  //  Yices2 and Princess when used in 2 distinct contexts

  @Test
  public void bvFormulasFromDistinctContextsEqualsTest() throws InvalidConfigurationException {
    requireBitvectors();

    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      BitvectorFormulaManager otherBvmgr =
          otherContext.getFormulaManager().getBitvectorFormulaManager();

      for (int length : new int[] {2, 4, 32, 64, 1000}) {
        assertThat(bvmgr.makeVariable(length, "x" + length))
            .isNotEqualTo(otherBvmgr.makeVariable(length, "x" + length));
        assertThat(otherBvmgr.makeVariable(length, "x" + length))
            .isNotEqualTo(bvmgr.makeVariable(length, "x" + length));
      }
    }
  }

  @Test
  public void intFormulasFromDistinctContextsEqualsTest() throws InvalidConfigurationException {
    requireIntegers();

    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      IntegerFormulaManager otherImgr = otherContext.getFormulaManager().getIntegerFormulaManager();

      for (int num : new int[] {-1, 0, 1, 2, 4, 32, 64, 1000}) {
        assertThat(imgr.makeVariable("x" + num)).isNotEqualTo(otherImgr.makeVariable("x" + num));
        assertThat(otherImgr.makeVariable("x" + num)).isNotEqualTo(imgr.makeVariable("x" + num));
      }
    }
  }

  @Test
  public void boolFormulasFromDistinctContextsEqualsTest() throws InvalidConfigurationException {
    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      BooleanFormulaManager otherBmgr = otherContext.getFormulaManager().getBooleanFormulaManager();

      assertThat(bmgr.makeVariable("name")).isNotEqualTo(otherBmgr.makeVariable("name"));
      assertThat(otherBmgr.makeVariable("name")).isNotEqualTo(bmgr.makeVariable("name"));
      assertThat(bmgr.makeVariable("tru")).isNotEqualTo(otherBmgr.makeTrue());
      assertThat(otherBmgr.makeVariable("tru")).isNotEqualTo(bmgr.makeTrue());
    }
  }

  // Yices2 and Princess share constants over contexts
  @Test
  public void boolConstantsFromDistinctContextsEqualsTest() throws InvalidConfigurationException {
    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      BooleanFormulaManager otherBmgr = otherContext.getFormulaManager().getBooleanFormulaManager();

      // TODO: add case for Yices2 and Princess. Either here or in a new test
      assertThat(bmgr.makeFalse()).isNotEqualTo(otherBmgr.makeFalse());
      assertThat(otherBmgr.makeFalse()).isNotEqualTo(bmgr.makeFalse());
      assertThat(bmgr.makeTrue()).isNotEqualTo(otherBmgr.makeTrue());
      assertThat(otherBmgr.makeTrue()).isNotEqualTo(bmgr.makeTrue());
    }
  }

  // Yices2 and Princess share constants over contexts
  @Test
  public void integerConstantsFromDistinctContextsEqualsTest()
      throws InvalidConfigurationException {
    requireIntegers();

    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      IntegerFormulaManager otherImgr = otherContext.getFormulaManager().getIntegerFormulaManager();

      // TODO: add case for Yices2 and Princess. Either here or in a new test
      for (int num : new int[] {-1, 0, 1, 2, 4, 32, 64, 1000}) {
        assertThat(imgr.makeNumber(num)).isNotEqualTo(otherImgr.makeNumber(num));
        assertThat(otherImgr.makeNumber(num)).isNotEqualTo(imgr.makeNumber(num));
        assertThat(imgr.makeNumber(num)).isNotEqualTo(otherImgr.makeNumber(num + 1));
        assertThat(otherImgr.makeNumber(num)).isNotEqualTo(imgr.makeNumber(num + 1));
        assertThat(imgr.makeNumber(num)).isNotEqualTo(otherImgr.makeNumber(num - 1));
        assertThat(otherImgr.makeNumber(num)).isNotEqualTo(imgr.makeNumber(num - 1));
      }
    }
  }

  // Yices2 and Princess share constants over contexts
  @Test
  public void bitvectorConstantsFromDistinctContextsEqualsTest()
      throws InvalidConfigurationException {
    requireBitvectors();

    try (SolverContext otherContext = SolverContextFactory.createSolverContext(solverToUse())) {
      BitvectorFormulaManager otherBvmgr =
          otherContext.getFormulaManager().getBitvectorFormulaManager();

      // TODO: add case for Yices2 and Princess. Either here or in a new test
      for (int length : new int[] {2, 4, 32, 64, 1000}) {
        assertThat(bvmgr.makeBitvector(length, 0))
            .isNotEqualTo(otherBvmgr.makeBitvector(length, 0));
        assertThat(otherBvmgr.makeBitvector(length, 0))
            .isNotEqualTo(bvmgr.makeBitvector(length, 0));
        assertThat(bvmgr.makeBitvector(length, 0))
            .isNotEqualTo(otherBvmgr.makeBitvector(length, 1));
        assertThat(otherBvmgr.makeBitvector(length, 0))
            .isNotEqualTo(bvmgr.makeBitvector(length, 1));
      }
    }
  }
}
