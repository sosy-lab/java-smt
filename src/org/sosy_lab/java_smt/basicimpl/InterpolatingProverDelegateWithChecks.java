/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This delegate enables common implementations for methods in {@link
 * InterpolatingProverEnvironment} based on the implementations in the abstract/theorem prover that
 * can not be done using abstract implementations. This class needs to be the first that is called
 * when using {@link InterpolatingProverEnvironment}s.
 */
class InterpolatingProverDelegateWithChecks<T>
    extends AbstractProverDelegateWithChecks<T, InterpolatingProverEnvironment<T>>
    implements InterpolatingProverEnvironment<T> {

  InterpolatingProverDelegateWithChecks(InterpolatingProverEnvironment<T> pBaseProver) {
    super(pBaseProver);
  }

  @SuppressWarnings("resource")
  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    getDelegateAsAbstractProver().checkGenerateInterpolants(formulasOfA);
    // TODO: do we want a common method to calculate partition B out of the asserted formulas
    //  efficiently? We currently have several distinct solutions.
    return delegate.getInterpolant(formulasOfA);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    getDelegateAsAbstractProver().checkGenerateSeqInterpolants(partitionedFormulas);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return delegate.getSeqInterpolants(partitionedFormulas);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    getDelegateAsAbstractProver()
        .checkGenerateTreeInterpolants(partitionedFormulas, startOfSubTree);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return delegate.getTreeInterpolants(partitionedFormulas, startOfSubTree);
  }
}
