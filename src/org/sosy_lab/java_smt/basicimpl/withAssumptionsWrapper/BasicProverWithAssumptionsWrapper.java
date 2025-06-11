// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

public class BasicProverWithAssumptionsWrapper<T, P extends BasicProverEnvironment<T>>
    implements BasicProverEnvironment<T> {

  protected final P delegate;
  protected final List<BooleanFormula> solverAssumptionsAsFormula = new ArrayList<>();

  BasicProverWithAssumptionsWrapper(P pDelegate) {
    delegate = pDelegate;
  }

  protected void clearAssumptions() {
    for (int i = 0; i < solverAssumptionsAsFormula.size(); i++) {
      delegate.pop();
    }
    solverAssumptionsAsFormula.clear();
  }

  protected void clearAssumptionsWithInterruptedException() throws InterruptedException {
    for (int i = 0; i < solverAssumptionsAsFormula.size(); i++) {
      try {
        delegate.pop();
      } catch (IllegalStateException ise) {
        if (ise.getMessage().startsWith(AbstractProver.SHUTDOWN_EXCEPTION_PREFIX)) {
          throw new InterruptedException(
              ise.getMessage()
                  .replace("Prover is not usable due " + "to shutdown with message: ", ""));
        }
      }
    }
    solverAssumptionsAsFormula.clear();
  }

  @Override
  public void pop() {
    clearAssumptions();
    delegate.pop();
  }

  @Override
  public T addConstraint(BooleanFormula constraint) throws InterruptedException {
    // This might throw the "wrong" exception because it pops the assumptions
    // (which does not return a InterruptedException for interrupts)
    clearAssumptionsWithInterruptedException();

    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    clearAssumptionsWithInterruptedException();
    delegate.push();
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    clearAssumptionsWithInterruptedException();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    clearAssumptionsWithInterruptedException();
    solverAssumptionsAsFormula.addAll(assumptions);
    for (BooleanFormula formula : assumptions) {
      registerPushedFormula(delegate.push(formula));
    }
    return delegate.isUnsat();
  }

  /** overridden in sub-class. */
  protected void registerPushedFormula(@SuppressWarnings("unused") T pPushResult) {}

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException {
    return delegate.getModelAssignments();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    clearAssumptions();
    return delegate.unsatCoreOverAssumptions(pAssumptions);
    //    if (isUnsatWithAssumptions(pAssumptions)) {
    //      // TODO project to pAssumptions?
    //      return Optional.of(getUnsatCore());
    //    } else {
    //      return Optional.empty();
    //    }
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public String toString() {
    return delegate.toString();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    clearAssumptionsWithInterruptedException();
    return delegate.allSat(pCallback, pImportant);
  }
}
