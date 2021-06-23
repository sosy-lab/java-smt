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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;

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
 * incremental solving, but is more complex to implement. Lets keep this idea is future work for
 * optimization.
 */
class Yices2TheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private static final int DEFAULT_PARAMS = 0; // use default setting in the solver

  protected final Yices2FormulaCreator creator;
  protected final long curEnv;
  protected final long curCfg;

  private final Deque<Set<Integer>> constraintStack = new ArrayDeque<>();

  private int stackSizeToUnsat = Integer.MAX_VALUE;

  protected Yices2TheoremProver(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pBmgr, pShutdownNotifier);
    this.creator = creator;
    curCfg = yices_new_config();
    yices_set_config(curCfg, "solver-type", "dpllt");
    yices_set_config(curCfg, "mode", "push-pop");
    curEnv = yices_new_context(curCfg);
    constraintStack.push(new LinkedHashSet<>()); // initial level
  }

  boolean isClosed() {
    return closed;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    if (constraintStack.size() <= stackSizeToUnsat) { // constraintStack and Yices stack have same
      // level.
      yices_pop(curEnv);
      stackSizeToUnsat = Integer.MAX_VALUE; // Reset stackSizeToUnsat as this pop() will bring the
      // stack into a pushable state if it was UNSAT before.
    }
    constraintStack.pop(); // Always pop constraintStack since it can get bigger than Yices stack.
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    int constraint = creator.extractInfo(pConstraint);
    if (!generateUnsatCores) { // unsat core does not work with incremental mode
      yices_assert_formula(curEnv, constraint);
    }
    constraintStack.peek().add(constraint);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    if (constraintStack.size() <= stackSizeToUnsat
        && yices_context_status(curEnv) != YICES_STATUS_UNSAT) {
      // Ensure that constraintStack and Yices stack are on the same level and Context is not UNSAT
      // from assertions since last push.
      yices_push(curEnv);
    } else if (stackSizeToUnsat == Integer.MAX_VALUE) {
      stackSizeToUnsat = constraintStack.size(); // if previous check fails and stackSizeToUnsat is
      // not already set, set it to the current stack
      // size before pushing.
    }
    constraintStack.push(new LinkedHashSet<>()); // Always push to ensure proper representation of
    // push actions, even if Yices did not push.
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    boolean unsat = false;
    if (generateUnsatCores) { // unsat core does not work with incremental mode
      int[] allConstraints = getAllConstraints();
      unsat =
          !yices_check_sat_with_assumptions(
              curEnv, DEFAULT_PARAMS, allConstraints.length, allConstraints, shutdownNotifier);
      return unsat;
    } else {
      unsat = !yices_check_sat(curEnv, DEFAULT_PARAMS, shutdownNotifier);
      if (unsat && stackSizeToUnsat == Integer.MAX_VALUE) {
        stackSizeToUnsat = constraintStack.size(); // If sat check is UNSAT and stackSizeToUnsat was
        // not already set, set to current
        // constraintStack size.
      }
      return unsat;
    }
  }

  private int[] getAllConstraints() {
    Set<Integer> allConstraints = new LinkedHashSet<>();
    constraintStack.forEach(allConstraints::addAll);
    return Ints.toArray(allConstraints);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    // TODO handle BooleanFormulaCollection / check for literals
    return !yices_check_sat_with_assumptions(
        curEnv, DEFAULT_PARAMS, pAssumptions.size(), uncapsulate(pAssumptions), shutdownNotifier);
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getModelWithoutChecks();
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
      constraintStack.clear();
      closed = true;
    }
  }

  @Override
  protected Model getModelWithoutChecks() {
    return new Yices2Model(yices_get_model(curEnv, 1), this, creator);
  }
}
