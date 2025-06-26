// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_itp_group;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_interpolant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_itp_group;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.primitives.Ints;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class Mathsat5InterpolatingProver extends Mathsat5AbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private static final ImmutableSet<String> ALLOWED_FAILURE_MESSAGES =
      ImmutableSet.of(
          "Unexpected proof rule to split: PN4msat5proof5ProofE",
          "impossible to build a suitable congruence graph!",
          "can't build ie-local interpolant",
          "set_raised on an already-raised proof",
          "splitting of AB-mixed terms not supported",
          "Hypothesis belongs neither to A nor to B",
          "FP<->BV combination unsupported by the current configuration",
          "cur_eq unknown to the classifier",
          "unknown constraint in the ItpMapper",
          "AB-mixed term not found in eq_itp map",
          "uncolored atom found in Array proof",
          "uncolorable Array proof",
          "arr: proof splitting not supported",
          "AB-mixed term in LaHyp",
          "AB-mixed term in LaCombImp");
  private static final ImmutableSet<String> ALLOWED_FAILURE_MESSAGE_PREFIXES =
      ImmutableSet.of("uncolorable NA lemma");

  Mathsat5InterpolatingProver(
      Mathsat5SolverContext pMgr,
      ShutdownNotifier pContextShutdownNotifier,
      @Nullable ShutdownNotifier pProverShutdownNotifier,
      Mathsat5FormulaCreator creator,
      Set<ProverOptions> options) {
    super(pMgr, options, creator, pContextShutdownNotifier, pProverShutdownNotifier);
  }

  @Override
  protected void createConfig(Map<String, String> pConfig) {
    pConfig.put("interpolation", "true");
    pConfig.put("model_generation", "true");
    pConfig.put("theory.bv.eager", "false");
  }

  @Override
  protected Integer addConstraintImpl(BooleanFormula f) throws InterruptedException {
    closeAllEvaluators();
    int group = msat_create_itp_group(curEnv);
    msat_set_itp_group(curEnv, group);
    long t = creator.extractInfo(f);
    msat_assert_formula(curEnv, t);
    return group;
  }

  @Override
  protected long getMsatModel() throws SolverException {
    // Interpolation in MathSAT is buggy at least for UFs+Ints and sometimes returns a wrong "SAT".
    // In this case, model generation fails and users should try again without interpolation.
    // Example failures: "Invalid model", "non-integer model value"
    // As this is a bug in MathSAT and not in our code, we throw a SolverException.
    // We do it only in InterpolatingProver because without interpolation this is not expected.
    try {
      return super.getMsatModel();
    } catch (IllegalArgumentException e) {
      String msg = Strings.emptyToNull(e.getMessage());
      throw new SolverException(
          "msat_get_model failed"
              + (msg != null ? " with \"" + msg + "\"" : "")
              + ", probably the actual problem is interpolation",
          e);
    }
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA)
      throws SolverException, InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    checkState(!wasLastSatCheckSat);
    checkState(!stackChangedSinceLastQuery);
    checkInterpolationArguments(formulasOfA);

    int[] groupsOfA = Ints.toArray(formulasOfA);
    long itp;
    try {
      itp = msat_get_interpolant(curEnv, groupsOfA);
    } catch (IllegalArgumentException e) {
      final String message = e.getMessage();
      if (!Strings.isNullOrEmpty(message)
          && (ALLOWED_FAILURE_MESSAGES.contains(message)
              || ALLOWED_FAILURE_MESSAGE_PREFIXES.stream().anyMatch(message::startsWith))) {
        // This is not a bug in our code,
        // but a problem of MathSAT which happens during interpolation
        throw new SolverException(message, e);
      }
      throw e;
    }
    return creator.encapsulateBoolean(itp);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas)
      throws SolverException, InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    checkState(!wasLastSatCheckSat);
    checkState(!stackChangedSinceLastQuery);
    Preconditions.checkArgument(
        !partitionedFormulas.isEmpty(), "at least one partition should be available.");
    final ImmutableSet<Integer> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitionedFormulas.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");

    // the fallback to a loop is sound and returns an inductive sequence of interpolants
    final List<BooleanFormula> itps = new ArrayList<>();
    for (int i = 1; i < partitionedFormulas.size(); i++) {
      itps.add(
          getInterpolant(
              ImmutableList.copyOf(Iterables.concat(partitionedFormulas.subList(0, i)))));
    }
    return itps;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException(
        "directly receiving tree interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important) {
    // TODO how can we support allsat in MathSat5-interpolation-prover?
    // error: "allsat is not compatible wwith proof generation"
    throw new UnsupportedOperationException(
        "allsat computation is not possible with interpolation prover.");
  }
}
