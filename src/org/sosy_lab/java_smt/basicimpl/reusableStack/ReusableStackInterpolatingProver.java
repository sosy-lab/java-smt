// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.reusableStack;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class ReusableStackInterpolatingProver<T>
    extends ReusableStackAbstractProver<T, InterpolatingProverEnvironment<T>>
    implements InterpolatingProverEnvironment<T> {

  public ReusableStackInterpolatingProver(InterpolatingProverEnvironment<T> pDelegate) {
    super(pDelegate);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    return delegate.getInterpolant(pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    return delegate.getSeqInterpolants(pPartitionedFormulas);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
  }
}
