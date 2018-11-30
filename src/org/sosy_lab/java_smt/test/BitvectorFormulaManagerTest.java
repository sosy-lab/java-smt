/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@RunWith(Parameterized.class)
public class BitvectorFormulaManagerTest extends SolverBasedTest0 {

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
    requireBitvectors();
  }

  @Test
  public void bvType() {
    for (int i : Lists.newArrayList(1, 2, 4, 32, 64, 1000)) {
      BitvectorType type = FormulaType.getBitvectorTypeWithSize(i);
      assertThat(type.getSize()).named("bitvector type size").isEqualTo(i);
      BitvectorFormula var = bvmgr.makeVariable(type, "x" + i);
      BitvectorType result = (BitvectorType) mgr.getFormulaType(var);
      assertThat(result.getSize()).named("bitvector size").isEqualTo(i);
    }
  }

  @Test
  public void bvOne() throws SolverException, InterruptedException {
    for (int i : Lists.newArrayList(1, 2, 4, 32, 64, 1000)) {
      BitvectorFormula var = bvmgr.makeVariable(i, "x" + i);
      BitvectorFormula num0 = bvmgr.makeBitvector(i, 0);
      BitvectorFormula num1 = bvmgr.makeBitvector(i, 1);
      assertThatFormula(bvmgr.equal(var, num0)).isSatisfiable();
      assertThatFormula(bvmgr.equal(var, num1)).isSatisfiable();
    }
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public void bvTooLargeNum() {
    bvmgr.makeBitvector(1, 2); // value 2 is too large for size 1
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvLargeNum() {
    bvmgr.makeBitvector(1, 1); // value 1 should be possible for size 1
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void bvSmallNum() {
    bvmgr.makeBitvector(1, -1); // value -1 should be possible for size 1
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public void bvTooSmallNum() {
    bvmgr.makeBitvector(1, -2); // value -2 is too small for size 1
  }

  @Test
  public void bvModelValue32bit() throws SolverException, InterruptedException {
    BitvectorFormula var = bvmgr.makeVariable(32, "var");

    Map<Long, Long> values = new LinkedHashMap<>();
    long int32 = 1L << 32;

    // positive signed values stay equal
    values.put(0L, 0L);
    values.put(1L, 1L);
    values.put(2L, 2L);
    values.put(123L, 123L);
    values.put((long) Integer.MAX_VALUE, (long) Integer.MAX_VALUE);

    // positive unsigned values stay equal
    values.put(Integer.MAX_VALUE + 1L, Integer.MAX_VALUE + 1l);
    values.put(Integer.MAX_VALUE + 2L, Integer.MAX_VALUE + 2L);
    values.put(Integer.MAX_VALUE + 123L, Integer.MAX_VALUE + 123L);
    values.put(int32 - 1L, int32 - 1);
    values.put(int32 - 2L, int32 - 2);
    values.put(int32 - 123L, int32 - 123);

    // negative signed values are converted to unsigned
    values.put(-1L, int32 - 1);
    values.put(-2L, int32 - 2);
    values.put(-123L, int32 - 123);
    values.put((long) Integer.MIN_VALUE, 1L + Integer.MAX_VALUE);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      for (Entry<Long, Long> entry : values.entrySet()) {
        prover.push(bvmgr.equal(var, bvmgr.makeBitvector(32, entry.getKey())));
        assertThat(prover).isSatisfiable();
        try (Model model = prover.getModel()) {
          Object value = model.evaluate(var);
          assertThat(value).isEqualTo(BigInteger.valueOf(entry.getValue()));
        }
        prover.pop();
      }
    }
  }
}
