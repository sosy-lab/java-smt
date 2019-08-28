/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_opt_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;

import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.sosy_lab.common.NativeLibraries;

public class Mathsat5OptimizationNativeApiTest extends Mathsat5AbstractNativeApiTeest {

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
