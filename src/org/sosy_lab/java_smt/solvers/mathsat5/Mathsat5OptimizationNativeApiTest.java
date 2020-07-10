// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_opt_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;

import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.sosy_lab.common.NativeLibraries;

public class Mathsat5OptimizationNativeApiTest extends Mathsat5AbstractNativeApiTest {

  @BeforeClass
  public static void loadMathsat() {
    try {
      NativeLibraries.loadLibrary("optimathsat5j");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("OptiMathSAT5 is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    long cfg = msat_create_config();
    env = msat_create_opt_env(cfg);
    msat_destroy_config(cfg);
  }
}
