/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.basicimpl.reusableStack;

import java.util.List;
import java.util.Set;
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
  public T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    return delegate.addConstraint(pConstraint);
  }

  @Override
  public BooleanFormula getInterpolant(List<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    return delegate.getInterpolant(pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    return delegate.getSeqInterpolants(pPartitionedFormulas);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
  }
}
