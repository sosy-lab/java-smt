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
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class DebuggingInterpolatingProverEnvironment<T> extends DebuggingBasicProverEnvironment<T>
    implements InterpolatingProverEnvironment<T> {
  private final InterpolatingProverEnvironment<T> delegate;
  private final DebuggingAssertions debugging;

  DebuggingInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate, DebuggingAssertions pDebugging) {
    super(pDelegate, pDebugging);
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.getInterpolant(formulasOfA);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    List<BooleanFormula> result = delegate.getSeqInterpolants(partitionedFormulas);
    for (BooleanFormula t : result) {
      debugging.addFormulaTerm(t);
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    List<BooleanFormula> result = delegate.getTreeInterpolants(partitionedFormulas, startOfSubTree);
    for (BooleanFormula t : result) {
      debugging.addFormulaTerm(t);
    }
    return result;
  }
}
