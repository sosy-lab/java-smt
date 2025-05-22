// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.Multimap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

class DebuggingBasicProverEnvironment<T> implements BasicProverEnvironment<T> {
  private final BasicProverEnvironment<T> delegate;
  private final DebuggingAssertions debugging;

  DebuggingBasicProverEnvironment(
      BasicProverEnvironment<T> pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public void pop() {
    debugging.assertThreadLocal();
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(constraint);
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    debugging.assertThreadLocal();
    delegate.push();
  }

  @Override
  public int size() {
    debugging.assertThreadLocal();
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    debugging.assertThreadLocal();
    return new DebuggingModel(delegate.getModel(), debugging);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    debugging.assertThreadLocal();
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    debugging.assertThreadLocal();
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : important) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.allSat(callback, important);
  }

  @Override
  public List<Multimap<BooleanFormula, T>> getInternalAssertedFormulas() {
    debugging.assertThreadLocal();
    return delegate.getInternalAssertedFormulas();
  }
}
