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

import com.google.common.base.Preconditions;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

abstract class StpAbstractProver<T> extends AbstractProver<T> {

  private final StpSolverContext context;
  private final StpFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  // private final long curConfig;
  protected final VC currVC;
  protected boolean closed;

  protected StpAbstractProver(
      StpSolverContext pContext,
      Set<ProverOptions> pOptions,
      StpFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    context = pContext;
    creator = pCreator;
    // curConfig = buildConfig(pOptions); //TODO implement configuration handling
    currVC = context.createEnvironment(null);// curConfig is to be passed in here
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    StpJavaApi.vc_pop(currVC);
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    // TODO update to use vc_query_with_timeout

    // To go this route I will have to implement the Stack for the "Constraints" ?!

    Preconditions.checkState(!closed);
    int result = StpJavaApi.checkSAT_old(currVC);
    try {
      if (result == 0) {
        return true;
      } else if (result == 1) {
        return false;
      } else if (result == 2) {
        throw new Exception("An error occured in STP during validation");
      }

      throw new Exception("An error occured in STP during validation");
    } catch (Exception e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return false;

    // throw new SolverException("NOT MPLEMENTED");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    // return false;
    throw new UnsupportedOperationException("Not implemented yet");
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
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
  public Model getModel() throws SolverException {
    // TODO Auto-generated method stub

    // I don't understand this model stuff.
    // return null;

    throw new UnsupportedOperationException("Not yet implemented");
  }

  @Override
  public void close() {
    if (!closed) {

      // TODO check if EXPRDELETE is set via vc_setInterfaceFlags
      // other we will can delete expression with vc_DeleteExpr
      StpJavaApi.vc_Destroy(currVC);
      closed = true;
    }
  }

}