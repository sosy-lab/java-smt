/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

class StpAbstractProver<T> extends AbstractProver<T> {

  protected StpAbstractProver(Set<ProverOptions> pOptions) {
    super(pOptions);
    // TODO Auto-generated constructor stub
  }

  @Override
  public void pop() {
    // TODO Auto-generated method stub

  }

  @Override
  public @Nullable T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void push() {
    // TODO Auto-generated method stub

  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public Model getModel() throws SolverException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Optional<List<BooleanFormula>>
      unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
          throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub

  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    return null;
  }

}
