// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.debugging.DebuggingSolverContext.NodeManager;

class DebuggingBasicProverEnvironment<T> extends FormulaChecks
    implements BasicProverEnvironment<T> {
  private final BasicProverEnvironment<T> delegate;

  DebuggingBasicProverEnvironment(BasicProverEnvironment<T> pDelegate, NodeManager pLocalFormulas) {
    super(pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public void pop() {
    assertThreadLocal();
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    assertThreadLocal();
    assertFormulaInContext(constraint);
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    assertThreadLocal();
    delegate.push();
  }

  @Override
  public int size() {
    assertThreadLocal();
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    assertThreadLocal();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      assertFormulaInContext(f);
    }
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    assertThreadLocal();
    return new DebuggingModel(delegate.getModel(), nodeManager);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    assertThreadLocal();
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      assertFormulaInContext(f);
    }
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    assertThreadLocal();
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    assertThreadLocal();
    for (BooleanFormula f : important) {
      assertFormulaInContext(f);
    }
    return delegate.allSat(callback, important);
  }
}
