// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolationPoint;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedInterpolatingProverEnvironment<T>
    extends SynchronizedBasicProverEnvironment<InterpolationPoint<T>>
    implements InterpolatingProverEnvironment<T> {

  private final InterpolatingProverEnvironment<T> delegate;

  SynchronizedInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate, SolverContext pSync) {
    super(pDelegate, pSync);
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<InterpolationPoint<T>> pFormulasOfA)
      throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.getInterpolant(pFormulasOfA);
    }
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<InterpolationPoint<T>>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.getSeqInterpolants(pPartitionedFormulas);
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<InterpolationPoint<T>>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
    }
  }
}
