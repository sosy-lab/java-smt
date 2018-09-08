/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.util.Set;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  private final boolean generateModels;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;

  protected AbstractProver(Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(
        generateModels, "Please set the prover option " + ProverOptions.GENERATE_MODELS + ".");
  }

  protected final void checkGenerateUnsatCores() {
    Preconditions.checkState(
        generateUnsatCores,
        "Please set the prover option " + ProverOptions.GENERATE_UNSAT_CORE + ".");
  }

  protected final void checkGenerateUnsatCoresOverAssumptions() {
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        "Please set the prover option " + ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS + ".");
  }
}
