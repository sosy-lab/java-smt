// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.util.Set;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  private final boolean generateModels;
  private final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;

  private static final String TEMPLATE = "Please set the prover option %s.";

  protected AbstractProver(Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = pOptions.contains(ProverOptions.GENERATE_ALL_SAT);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
  }

  protected final void checkGenerateAllSat() {
    Preconditions.checkState(generateAllSat, TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  protected final void checkGenerateUnsatCores() {
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
  }

  protected final void checkGenerateUnsatCoresOverAssumptions() {
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
  }

  protected final void checkEnableSeparationLogic() {
    Preconditions.checkState(enableSL, TEMPLATE, ProverOptions.ENABLE_SEPARATION_LOGIC);
  }
}
