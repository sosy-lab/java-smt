// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Preconditions;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.boolector.BtorJNI.TerminationCallback;

abstract class BoolectorAbstractProver<T> extends AbstractProverWithAllSat<T> {
  // BoolectorAbstractProver<E, AF> extends AbstractProverWithAllSat<E>
  // AF = assertedFormulas; E = ?

  /** Boolector does not support multiple solver stacks. */
  private final AtomicBoolean isAnyStackAlive;

  private final long btor;
  private final BoolectorFormulaManager manager;
  private final BoolectorFormulaCreator creator;
  protected final Deque<List<Long>> assertedFormulas = new ArrayDeque<>();
  protected boolean wasLastSatCheckSat = false; // and stack is not changed
  private final TerminationCallback terminationCallback;
  private final long terminationCallbackHelper;

  // Used/Built by TheoremProver
  protected BoolectorAbstractProver(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator,
      long btor,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      AtomicBoolean pIsAnyStackAlive) {
    super(pOptions, manager.getBooleanFormulaManager(), pShutdownNotifier);
    this.manager = manager;
    this.creator = creator;
    this.btor = btor;
    terminationCallback = shutdownNotifier::shouldShutdown;
    terminationCallbackHelper = addTerminationCallback();

    isAnyStackAlive = pIsAnyStackAlive;
    // avoid dual stack usage
    Preconditions.checkState(
        !isAnyStackAlive.getAndSet(true),
        "Boolector does not support the usage of multiple "
            + "solver stacks at the same time. Please close any existing solver stack.");
  }

  @Override
  public void close() {
    if (!closed) {
      // Free resources of callback
      BtorJNI.boolector_free_termination(terminationCallbackHelper);
      BtorJNI.boolector_pop(manager.getEnvironment(), assertedFormulas.size());
      assertedFormulas.clear();
      // You can't use delete here because you wouldn't be able to access model
      // Wait till we have visitor/toList, after that we can delete here
      // BtorJNI.boolector_delete(btor);
      closed = true;
      Preconditions.checkState(isAnyStackAlive.getAndSet(false));
    }
  }

  /*
   * Boolector should throw its own exceptions that tell you what went wrong!
   */
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    final int result = BtorJNI.boolector_sat(btor);
    if (result == BtorJNI.BTOR_RESULT_SAT_get()) {
      wasLastSatCheckSat = true;
      return false;
    } else if (result == BtorJNI.BTOR_RESULT_UNSAT_get()) {
      return true;
    } else if (result == BtorJNI.BTOR_RESULT_UNKNOWN_get()) {
      if (BtorJNI.boolector_terminate(btor) == 0) {
        throw new SolverException(
            "Boolector has encountered a problem or ran out of stack or heap memory, "
                + "try increasing their sizes.");
      } else {
        throw new InterruptedException("Boolector was terminated via ShutdownManager.");
      }
    } else {
      throw new SolverException("Boolector sat call returned " + result);
    }
  }

  @Override
  public void pop() {
    assertedFormulas.pop();
    BtorJNI.boolector_pop(manager.getEnvironment(), 1);
  }

  @Override
  public void push() {
    assertedFormulas.push(new ArrayList<>());
    BtorJNI.boolector_push(manager.getEnvironment(), 1);
  }

  @Override
  public int size() {
    return assertedFormulas.size();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    for (BooleanFormula assumption : pAssumptions) {
      BtorJNI.boolector_assume(btor, BoolectorFormulaManager.getBtorTerm(assumption));
    }
    return isUnsat();
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    return getModelWithoutChecks();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException("Unsat core is not supported by Boolector.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "Unsat core with assumptions is not supported by Boolector.");
  }

  @Override
  protected Model getModelWithoutChecks() {
    return new BoolectorModel(btor, creator, this, getAssertedTerms());
  }

  @Override
  @Nullable
  public T addConstraint(BooleanFormula constraint) {
    BtorJNI.boolector_assert(
        manager.getEnvironment(), BoolectorFormulaManager.getBtorTerm(constraint));
    assertedFormulas.peek().add(BoolectorFormulaManager.getBtorTerm(constraint));
    return null;
  }

  protected Collection<Long> getAssertedTerms() {
    List<Long> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }

  /**
   * Simply returns true if the prover is closed. False otherwise.
   *
   * @return bool return value.
   */
  protected boolean isClosed() {
    return closed;
  }

  private long addTerminationCallback() {
    Preconditions.checkState(!closed, "solver context is already closed");
    return BtorJNI.boolector_set_termination(btor, terminationCallback);
  }
}
