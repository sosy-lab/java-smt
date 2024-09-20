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

import static com.google.common.truth.Truth.assertThat;

import org.junit.Test;
import org.sosy_lab.java_smt.api.BitvectorFormula;

public class RotationVisitorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Test
  public void rotateLeftTest() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeBitvector(8, 7);
    assertThat(mgr.extractVariables(bvmgr.rotateLeft(x, 1))).isEmpty();
  }

  @Test
  public void rotateRightTest() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeBitvector(8, 7);
    assertThat(mgr.extractVariables(bvmgr.rotateRight(x, 1))).isEmpty();
  }

  @Test
  public void rotateLeftIntegerTest() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeBitvector(8, 7);
    BitvectorFormula y = bvmgr.makeBitvector(8, 1);
    assertThat(mgr.extractVariables(bvmgr.rotateLeft(x, y))).isEmpty();
  }

  @Test
  public void rotateRightIntegerTest() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeBitvector(8, 7);
    BitvectorFormula y = bvmgr.makeBitvector(8, 1);
    assertThat(mgr.extractVariables(bvmgr.rotateRight(x, y))).isEmpty();
  }
}
