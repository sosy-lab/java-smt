/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.cvc4;

import com.google.common.base.Preconditions;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;

import java.util.List;
import java.util.Set;

public class CVC4InterpolatingProver extends CVC4AbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  protected CVC4InterpolatingProver(CVC4FormulaManager pMgr) {
    super(pMgr);
  }

  @Override
  public Integer addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);

    // TODO result value and assertion in partitions
    smtEngine.assertFormula(mgr.extractInfo(f));
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    smtEngine.push();
  }

  @Override
  public Integer push(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    push();
    return addConstraint(pF);
  }

  @Override
  public BooleanFormula getInterpolant(List<Integer> pFormulasOfA) throws SolverException {
    Preconditions.checkState(!closed);
    return null;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<Integer>> pPartitionedFormulas) {
    throw new UnsupportedOperationException();
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Integer>> pPartitionedFormulas, int[] pStartOfSubTree) {
    throw new UnsupportedOperationException();
  }
}
