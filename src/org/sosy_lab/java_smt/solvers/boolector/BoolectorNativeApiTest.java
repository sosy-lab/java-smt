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
package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableMap;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext.SatSolver;

public class BoolectorNativeApiTest {

  private long btor;

  @BeforeClass
  public static void load() {
    try {
      NativeLibraries.loadLibrary("boolector");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Boolector is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    btor = BtorJNI.boolector_new();
  }

  @After
  public void freeEnvironment() {
    BtorJNI.boolector_delete(btor);
  }

  // some options have a different name in the API that their internal representation.
  // TODO why?
  private static final ImmutableMap<String, String> ALLOWED_DIFFS =
      ImmutableMap.<String, String>builder()
          .put("BTOR_OPT_ACKERMANNIZE", "BTOR_OPT_ACKERMANN")
          .put("BTOR_OPT_QUANT_DUAL", "BTOR_OPT_QUANT_DUAL_SOLVER")
          .put("BTOR_OPT_QUANT_SYNTHLIMIT", "BTOR_OPT_QUANT_SYNTH_LIMIT")
          .put("BTOR_OPT_QUANT_SYNTHQI", "BTOR_OPT_QUANT_SYNTH_QI")
          .put("BTOR_OPT_QUANT_MS", "BTOR_OPT_QUANT_MINISCOPE")
          .put("BTOR_OPT_DEFAULT_CADICAL", "BTOR_OPT_DEFAULT_TO_CADICAL")
          .put("BTOR_OPT_QUANT_SYNTHCOMPLETE", "BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE")
          .put("BTOR_OPT_BETA_REDUCE", "BTOR_OPT_BETA_REDUCE_ALL")
          .build();

  @Test
  public void optionNameTest() {
    // check whether our enum is identical to Boolector's internal enum
    for (BtorOption option : BtorOption.values()) {
      String optName = BtorJNI.boolector_get_opt_lng(btor, option.getValue());
      String converted = "BTOR_OPT_" + optName.replace("-", "_").replace(":", "_").toUpperCase();
      // System.out.println("our option: " + option + " -- their option: " + optName);
      assertThat(option.name()).isEqualTo(ALLOWED_DIFFS.getOrDefault(converted, converted));
    }
  }

  @Test
  public void satSolverTest() {
    // check whether all sat solvers are available
    for (SatSolver satSolver : SatSolver.values()) {
      long btor1 = BtorJNI.boolector_new();
      BtorJNI.boolector_set_sat_solver(btor1, satSolver.name().toLowerCase());
      long newVar = BtorJNI.boolector_var(btor1, BtorJNI.boolector_bool_sort(btor1), "x");
      BtorJNI.boolector_assert(btor1, newVar);
      int result = BtorJNI.boolector_sat(btor1);
      assertThat(result).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());
      BtorJNI.boolector_delete(btor1);
    }
  }
}
