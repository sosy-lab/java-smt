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

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;

/**
 * TODO use the class to settings or config OR BETTER DELETE IT
 *
 * <p>This class is the actual Wrapper around an STP "context" known over there as Validity Checker
 * All "context" related operations are handled here Flags, SAT solver settings, STP "environment"
 * variables are handled here
 *
 * <p>Note the "context" here differs from the 'Context class'
 */
class StpEnvironment {

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  // private final VC vcStpContext;

  public StpEnvironment(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pStpLogfile,
      long pRandomSeed) {

    this.logger = pLogger;
    this.shutdownNotifier = pShutdownNotifier;

    // create VC (ie context)
    // vcStpContext = stpJapi.vc_createValidityChecker();

  }

  // public long getVC() {
  // return StpVC.getEnv(vcStpContext);
  // }

}
