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
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class StpTheoremProver extends StpAbstractProver<Void> implements ProverEnvironment {

  protected StpTheoremProver(
      StpSolverContext pContext,
      ShutdownNotifier pShutdownNotifier,
      StpFormulaCreator pFrmcreator,
      Set<ProverOptions> pOptions) {
    super(pContext, pOptions, pFrmcreator, pShutdownNotifier);
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    Preconditions.checkState(!closed);

    StpJavaApi.addAssertFormula(currVC, StpFormulaManager.getStpTerm(pConstraint));
    return null;
  }

}
