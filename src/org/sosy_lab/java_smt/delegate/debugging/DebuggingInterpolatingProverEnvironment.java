// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class DebuggingInterpolatingProverEnvironment<T> extends DebuggingBasicProverEnvironment<T>
    implements InterpolatingProverEnvironment<T> {
  private final InterpolatingProverEnvironment<T> delegate;

  public DebuggingInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate, Set<Formula> pLocalFormulas) {
    super(pDelegate, pLocalFormulas);
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    // FIXME: We should probably check that the formula ids are valid
    return delegate.getInterpolant(formulasOfA);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    return delegate.getSeqInterpolants(partitionedFormulas);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    return delegate.getTreeInterpolants(partitionedFormulas, startOfSubTree);
  }
}
