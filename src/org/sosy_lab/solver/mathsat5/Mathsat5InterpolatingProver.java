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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_check_sat_with_assumptions;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_itp_group;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_interpolant;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_itp_group;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

class Mathsat5InterpolatingProver extends Mathsat5AbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private static final Collection<String> ALLOWED_FAILURE_MESSAGES =
      ImmutableList.of(
          "impossible to build a suitable congruence graph",
          "can't build ie-local interpolant",
          "splitting of AB-mixed terms not supported",
          "Hypothesis belongs neither to A nor to B",
          "FP<->BV combination unsupported by the current configuration",
          "cur_eq unknown to the classifier",
          "unknown constraint in the ItpMapper",
          "AB-mixed term not found in eq_itp map");

  Mathsat5InterpolatingProver(Mathsat5SolverContext pMgr, Mathsat5FormulaCreator creator) {
    super(pMgr, createConfig(), creator);
  }

  private static Map<String, String> createConfig() {
    return ImmutableMap.<String, String>builder()
        .put("interpolation", "true")
        .put("model_generation", "true")
        .put("theory.bv.eager", "false")
        .build();
  }

  @Override
  public Integer addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    int group = msat_create_itp_group(curEnv);
    msat_set_itp_group(curEnv, group);
    long t = creator.extractInfo(f);
    msat_assert_formula(curEnv, t);
    return group;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    msat_push_backtrack_point(curEnv);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    try {
      long[] assumptions =
          Longs.toArray(Collections2.transform(pAssumptions, Mathsat5FormulaManager::getMsatTerm));
      return !msat_check_sat_with_assumptions(curEnv, assumptions);
    } catch (IllegalStateException e) {
      handleSolverExceptionInUnsatCheck(e);
      throw e;
    }
  }

  @Override
  public BooleanFormula getInterpolant(List<Integer> formulasOfA) throws SolverException {
    Preconditions.checkState(!closed);

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
      if (ALLOWED_FAILURE_MESSAGES.stream().anyMatch(msg::contains)) {
        // This is not a bug in our code,
        // but a problem of MathSAT which happens during interpolation
        throw new SolverException(e.getMessage(), e);
      }
      throw e;
    }
    return creator.encapsulateBoolean(itp);
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
        "directly receiving tree interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }
}
