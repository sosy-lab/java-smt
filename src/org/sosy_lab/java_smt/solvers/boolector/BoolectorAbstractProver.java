// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import java.io.IOException;
import java.util.Collection;
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
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.solvers.boolector.BtorJNI.TerminationCallback;

abstract class BoolectorAbstractProver<T> extends AbstractProverWithAllSat<T> {

  /** Boolector does not support multiple solver stacks. */
  private final AtomicBoolean isAnyStackAlive;

  private final long btor;
  private final BoolectorFormulaManager manager;
  private final BoolectorFormulaCreator creator;
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
    // push an initial level, required for cleaning up later (see #close), for reusage of Boolector.
    BtorJNI.boolector_push(manager.getEnvironment(), 1);
  }

  @Override
  public void close() {
    if (!closed) {
      // Free resources of callback
      BtorJNI.boolector_free_termination(terminationCallbackHelper);
      // remove the whole stack, including the initial level from the constructor call.
      BtorJNI.boolector_pop(manager.getEnvironment(), size() + 1);
      // You can't use delete here because you wouldn't be able to access model
      // Wait till we have visitor/toList, after that we can delete here
      // BtorJNI.boolector_delete(btor);
      Preconditions.checkState(isAnyStackAlive.getAndSet(false));
    }
    super.close();
  }

  /*
   * Boolector should throw its own exceptions that tell you what went wrong!
   */
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    if (Generator.isLoggingEnabled()) {
      try {
        Generator.dumpSMTLIB2();
      } catch (IOException pE) {
        // FIXME Find a better way to handle the IOException
        throw new RuntimeException(pE);
      }
    }
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
  protected void popImpl() {
    BtorJNI.boolector_pop(manager.getEnvironment(), 1);
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    BtorJNI.boolector_push(manager.getEnvironment(), 1);
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

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected BoolectorModel getEvaluatorWithoutChecks() {
    return new BoolectorModel(
        btor, creator, this, Collections2.transform(getAssertedFormulas(), creator::extractInfo));
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
  @Nullable
  protected T addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    BtorJNI.boolector_assert(
        manager.getEnvironment(), BoolectorFormulaManager.getBtorTerm(constraint));
    return null;
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
