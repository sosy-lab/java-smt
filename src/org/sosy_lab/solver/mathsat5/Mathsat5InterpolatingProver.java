/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_itp_group;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_interpolant;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_copy_from;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_itp_group;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_option_checked;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;

import java.util.List;
import java.util.Set;

class Mathsat5InterpolatingProver extends Mathsat5AbstractProver
    implements InterpolatingProverEnvironmentWithAssumptions<Integer> {

  private final boolean useSharedEnv;

  Mathsat5InterpolatingProver(Mathsat5FormulaManager pMgr, boolean shared) {
    super(pMgr, createConfig(), shared, false);
    useSharedEnv = shared;
  }

  private static long createConfig() {
    long cfg = msat_create_config();
    msat_set_option_checked(cfg, "interpolation", "true");
    msat_set_option_checked(cfg, "model_generation", "true");
    msat_set_option_checked(cfg, "theory.bv.eager", "false");

    return cfg;
  }

  @Override
  public Integer push(BooleanFormula f) {
    Preconditions.checkState(curEnv != 0);
    long t = Mathsat5FormulaManager.getMsatTerm(f);
    //long t = ((Mathsat5Formula)f).getTerm();
    if (!useSharedEnv) {
      t = msat_make_copy_from(curEnv, t, mgr.getEnvironment());
    }
    int group = msat_create_itp_group(curEnv);
    msat_push_backtrack_point(curEnv);
    msat_set_itp_group(curEnv, group);
    msat_assert_formula(curEnv, t);
    return group;
  }

  @Override
  public BooleanFormula getInterpolant(List<Integer> formulasOfA) throws SolverException {
    Preconditions.checkState(curEnv != 0);

    int[] groupsOfA = new int[formulasOfA.size()];
    int i = 0;
    for (Integer f : formulasOfA) {
      groupsOfA[i++] = f;
    }

    long itp;
    try {
      itp = msat_get_interpolant(curEnv, groupsOfA);
    } catch (IllegalArgumentException e) {
      String msg = Strings.nullToEmpty(e.getMessage());
      if (msg.contains("impossible to build a suitable congruence graph")
          || msg.contains("can't build ie-local interpolant")
          || msg.contains("splitting of AB-mixed terms not supported")
          || msg.contains("Hypothesis belongs neither to A nor to B")) {
        // This is not a bug in our code,
        // but a problem of MathSAT which happens during interpolation
        throw new SolverException(e.getMessage(), e);
      }
      throw e;
    }

    if (!useSharedEnv) {
      itp = msat_make_copy_from(mgr.getEnvironment(), itp, curEnv);
    }
    return mgr.encapsulateBooleanFormula(itp);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<Integer>> partitionedFormulas) {
    // TODO is fallback to loop sound?

    //final List<BooleanFormula> itps = new ArrayList<>();
    //for (int i = 0; i < partitionedFormulas.size(); i++) {
    //  itps.add(getInterpolant(
    //      Lists.newArrayList(Iterables.concat(partitionedFormulas.subList(0, i)))));
    //}
    //return itps;

    throw new UnsupportedOperationException(
        "directly receiving an inductive sequence of interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Integer>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException(
        "directly receiving of tree interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }
}
