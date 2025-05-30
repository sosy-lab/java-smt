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
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

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

  @Override
  public void pop() {
    clearAssumptions();
    delegate.pop();
  }

  @Override
  public T addConstraint(BooleanFormula constraint) throws InterruptedException {
    clearAssumptions();
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    clearAssumptions();
    delegate.push();
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    clearAssumptions();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    clearAssumptions();
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
    clearAssumptions();
    return delegate.allSat(pCallback, pImportant);
  }

  @Override
  public ShutdownManager getShutdownManagerForProver() throws UnsupportedOperationException {
    return delegate.getShutdownManagerForProver();
  }
}
