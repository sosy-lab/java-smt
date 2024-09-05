// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_OPTIMUM;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_objective;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_load_objective_model;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_maximize;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_minimize;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_value_is_unbounded;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_value_term;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class Mathsat5OptimizationProver extends Mathsat5AbstractProver<Formula>
    implements OptimizationProverEnvironment {

  private static final int ERROR_TERM = 0;
  private final UniqueIdGenerator idGenerator = new UniqueIdGenerator();

  /**
   * ID given to user -> number of the objective. Size corresponds to the number of currently
   * existing objectives.
   */
  private PersistentMap<Integer, Long> objectiveMap = PathCopyingPersistentTreeMap.of();

  /** Stack of the objective maps. Some duplication, but shouldn't be too important. */
  private final Deque<PersistentMap<Integer, Long>> stack = new ArrayDeque<>();

  Mathsat5OptimizationProver(
      Mathsat5SolverContext pMgr,
      ShutdownNotifier pShutdownNotifier,
      Mathsat5FormulaCreator creator,
      Set<ProverOptions> options) {
    super(pMgr, options, creator, pShutdownNotifier);
  }

  @Override
  protected void createConfig(Map<String, String> pConfig) {
    pConfig.put("model_generation", "true");
  }

  @Override
  protected Formula addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    msat_assert_formula(curEnv, getMsatTerm(constraint));
    return constraint;
  }

  @Override
  public int maximize(Formula objective) {
    checkState(!closed);
    long objectiveId = msat_make_maximize(curEnv, getMsatTerm(objective));
    msat_assert_objective(curEnv, objectiveId);
    int id = idGenerator.getFreshId(); // mapping needed to avoid long-int-conversion
    objectiveMap = objectiveMap.putAndCopy(id, objectiveId);
    return id;
  }

  @Override
  public int minimize(Formula objective) {
    checkState(!closed);
    long objectiveId = msat_make_minimize(curEnv, getMsatTerm(objective));
    msat_assert_objective(curEnv, objectiveId);
    int id = idGenerator.getFreshId(); // mapping needed to avoid long-int-conversion
    objectiveMap = objectiveMap.putAndCopy(id, objectiveId);
    return id;
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    checkState(!closed);
    final boolean isSatisfiable = msat_check_sat(curEnv);
    if (isSatisfiable) {
      return OptStatus.OPT;
    } else {
      return OptStatus.UNSAT;
    }
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    super.pushImpl();
    stack.add(objectiveMap);
  }

  @Override
  protected void popImpl() {
    objectiveMap = stack.pop();
    super.popImpl();
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    checkState(!closed);
    return getValue(handle, epsilon);
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    checkState(!closed);
    return getValue(handle, epsilon);
  }

  private Optional<Rational> getValue(int handle, Rational epsilon) {
    assert objectiveMap.containsKey(handle) : "querying an unknown handle";
    long objective = objectiveMap.get(handle);
    int isUnbounded = msat_objective_value_is_unbounded(curEnv, objective, MSAT_OPTIMUM);
    if (isUnbounded == 1) {
      return Optional.empty();
    }
    assert isUnbounded == 0;
    long epsilonTerm = msat_make_number(curEnv, epsilon.toString());
    long objectiveValue =
        msat_objective_value_term(curEnv, objective, MSAT_OPTIMUM, ERROR_TERM, epsilonTerm);
    return Optional.of(Rational.ofString(msat_term_repr(objectiveValue)));
  }

  @Override
  public Model getModel() throws SolverException {
    checkState(!closed);
    if (!objectiveMap.isEmpty()) {
      msat_load_objective_model(curEnv, objectiveMap.values().iterator().next());
    }
    return super.getModel();
  }
}
