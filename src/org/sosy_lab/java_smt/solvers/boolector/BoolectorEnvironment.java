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
package org.sosy_lab.java_smt.solvers.boolector;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class BoolectorEnvironment {

  private final int randomSeed;
  private final @Nullable PathCounterTemplate basicLogfile;
  private final ShutdownNotifier shutdownNotifier;

  private final long btor;

  private final List<BoolectorAbstractProver<?>> registeredProvers = new ArrayList<>();

  BoolectorEnvironment(
      Configuration config,
      @Nullable final PathCounterTemplate pBasicLogfile,
      ShutdownNotifier pShutdownNotifier,
      final int pRandomSeed)
      throws InvalidConfigurationException {

    config.inject(this);

    basicLogfile = pBasicLogfile;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;

    btor = getNewBtor();
  }

  /**
   * This method returns a new prover, that is registered in this environment. All variables are
   * shared in all registered Boolector instances(btor).
   */
  BoolectorAbstractProver<?> getNewProver(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator,
      Set<ProverOptions> pOptions) {
    // create new btor and copy all nodes etc. because clone doesnt work with all sat solvers
    long newBtor = getNewBtor();

    // clone Btor for quick test without stack
    newBtor = BtorJNI.boolector_clone(btor);

    // Options for prover
    // Atm just enable model gen, later use Options
    BtorJNI.boolector_set_opt(newBtor, BtorOption.BTOR_OPT_MODEL_GEN.swigValue(), 1);

    BoolectorAbstractProver<Long> prover =
        new BoolectorTheoremProver(manager, creator, newBtor, shutdownNotifier, pOptions);
    registeredProvers.add(prover);
    return prover;
  }

  private long getNewBtor() {
    return BtorJNI.boolector_new();
    // set options HERE for btor
  }

  public Long getBtor() {
    return btor;
  }

  public Long getBoolSort() {
    return BtorJNI.boolector_bool_sort(btor);
  }
}
