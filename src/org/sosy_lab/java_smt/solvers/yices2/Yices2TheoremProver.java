// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_STATUS_UNSAT;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_assert_formula;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_sat;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_sat_with_assumptions;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_context_status;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_unsat_core;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_pop;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_push;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config;

import com.google.common.base.Preconditions;
import com.google.common.primitives.Ints;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;

/**
 * Info about the option {@link ProverOptions#GENERATE_UNSAT_CORE}: Yices provides the unsat core
 * only for additional formulae, not for already asserted ones. Thus, we have two possible
 * solutions:
 *
 * <p>1) Avoid incremental solving and simply provide all formulae as additional ones. Currently
 * implemented this way.
 *
 * <p>2) Add additional boolean symbols 'p', add a constraint 'p=f' for each asserted formula 'f',
 * compute the unsat core over all 'p's, and match them back to their formula 'f'. This allows
 * incremental solving, but is more complex to implement. Let's keep this idea is future work for
 * optimization.
 */
class Yices2TheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private static final int DEFAULT_PARAMS = 0; // use default setting in the solver

  protected final FormulaManager manager;
  protected final Yices2FormulaCreator creator;

  protected final long curEnv;
  protected final long curCfg;

  // Yices does not allow to PUSH when the stack is UNSAT.
  // Therefore, we need to keep track of all added constraints beyond that stack-level.
  private int stackSizeToUnsat = Integer.MAX_VALUE;

  protected Yices2TheoremProver(
      FormulaManager pFormulaManager,
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pFormulaManager.getBooleanFormulaManager(), pShutdownNotifier);
    this.creator = creator;
    this.manager = pFormulaManager;
    curCfg = yices_new_config();
    yices_set_config(curCfg, "solver-type", "dpllt");
    yices_set_config(curCfg, "mode", "push-pop");
    curEnv = yices_new_context(curCfg);
  }

  boolean isClosed() {
    return closed;
  }

  @Override
  protected void popImpl() {
    if (size() < stackSizeToUnsat) { // constraintStack and Yices stack have same level.
      yices_pop(curEnv);
      // Reset stackSizeToUnsat to bring the stack into a pushable state if it was UNSAT before.
      stackSizeToUnsat = Integer.MAX_VALUE;
    }
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula pConstraint)
      throws InterruptedException {
    if (!generateUnsatCores) { // unsat core does not work with incremental mode
      int constraint = creator.extractInfo(pConstraint);
      yices_assert_formula(curEnv, constraint);
    }
    return null;
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    if (size() < stackSizeToUnsat && yices_context_status(curEnv) != YICES_STATUS_UNSAT) {
      // Ensure that constraintStack and Yices stack are on the same level
      // and Context is not UNSAT from assertions since last push.
      yices_push(curEnv);
    } else if (stackSizeToUnsat == Integer.MAX_VALUE) {
      // if previous check fails and stackSizeToUnsat is
      // not already set, set it to the current stack-size before pushing.
      stackSizeToUnsat = size();
    }
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    boolean unsat;
    if (generateUnsatCores) { // unsat core does not work with incremental mode
      int[] allConstraints = getAllConstraints();
      unsat =
          !yices_check_sat_with_assumptions(
              curEnv, DEFAULT_PARAMS, allConstraints.length, allConstraints, shutdownNotifier);
    } else {
      unsat = !yices_check_sat(curEnv, DEFAULT_PARAMS, shutdownNotifier);
      if (unsat && stackSizeToUnsat == Integer.MAX_VALUE) {
        stackSizeToUnsat = size();
        // If sat check is UNSAT and stackSizeToUnsat waS not already set,
        // set to current constraintStack size.
      }
    }
    return unsat;
  }

  private int[] getAllConstraints() {
    return Ints.toArray(
        getAssertedFormulas().stream().map(creator::extractInfo).collect(Collectors.toSet()));
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    // TODO handle BooleanFormulaCollection / check for literals
    return !yices_check_sat_with_assumptions(
        curEnv, DEFAULT_PARAMS, pAssumptions.size(), uncapsulate(pAssumptions), shutdownNotifier);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected Yices2Model getEvaluatorWithoutChecks() {
    return new Yices2Model(manager, yices_get_model(curEnv, 1), this, creator);
  }

  private List<BooleanFormula> encapsulate(int[] terms) {
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (int t : terms) {
      result.add(creator.encapsulateBoolean(t));
    }
    return result;
  }

  private int[] uncapsulate(Collection<BooleanFormula> terms) {
    int[] result = new int[terms.size()];
    int i = 0;
    for (BooleanFormula t : terms) {
      result[i++] = creator.extractInfo(t);
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    return getUnsatCore0();
  }

  private List<BooleanFormula> getUnsatCore0() {
    return encapsulate(yices_get_unsat_core(curEnv));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Preconditions.checkState(!isClosed());
    checkGenerateUnsatCoresOverAssumptions();
    boolean sat = !isUnsatWithAssumptions(pAssumptions);
    return sat ? Optional.empty() : Optional.of(getUnsatCore0());
  }

  @Override
  public void close() {
    if (!closed) {
      yices_free_context(curEnv);
      yices_free_config(curCfg);
      stackSizeToUnsat = Integer.MAX_VALUE;
    }
    super.close();
  }
}
