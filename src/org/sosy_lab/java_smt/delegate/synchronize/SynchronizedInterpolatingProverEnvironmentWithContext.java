// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedInterpolatingProverEnvironmentWithContext<T>
    extends SynchronizedBasicProverEnvironmentWithContext<T>
    implements InterpolatingProverEnvironment<T> {

  private final InterpolatingProverEnvironment<T> delegate;

  SynchronizedInterpolatingProverEnvironmentWithContext(
      InterpolatingProverEnvironment<T> pDelegate,
      SolverContext pSync,
      FormulaManager pManager,
      FormulaManager pOtherManager) {
    super(pDelegate, pSync, pManager, pOtherManager);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    return manager.translateFrom(delegate.getInterpolant(pFormulasOfA), otherManager);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    return translate(delegate.getSeqInterpolants(pPartitionedFormulas), otherManager, manager);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    return translate(
        delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree), otherManager, manager);
  }
}
