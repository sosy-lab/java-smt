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

import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableMap;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

@Options(prefix = "solver.boolector")
class BoolectorEnvironment {

  @Option(
    secure = true,
    description = "The SAT solver used by Boolector. Available are \"Lingeling\", \"PicoSAT\" and \"MiniSAT \". Please enter the String for the Solver you want (case insensitive).")
  private String satSolver = "";

  @Option(
    secure = true,
    description = "Further options for Boolector in addition to the default options. "
        + "Format:  \"Optionname=value\" with ’,’ to seperate options. "
        + "Optionname and value can be found in BtorOption or Boolector C Api."
        + "Example: \"BTOR_OPT_MODEL_GEN=2,BTOR_OPT_INCREMENTAL=1\".")
  private String furtherOptions = "";

  private final int randomSeed;
  private final @Nullable PathCounterTemplate basicLogfile;
  private final ShutdownNotifier shutdownNotifier;

  private final long btor;

  BoolectorEnvironment(
      Configuration config,
      @Nullable final PathCounterTemplate pBasicLogfile,
      ShutdownNotifier pShutdownNotifier,
      final int pRandomSeed)
      throws InvalidConfigurationException {

    basicLogfile = pBasicLogfile;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;

    try {
      NativeLibraries.loadLibrary("boolector");
    } catch (UnsatisfiedLinkError e) {
      System.err.println("Boolector library could not be loaded.");
    }

    btor = BtorJNI.boolector_new();
    config.inject(this);
    // Setting SAT Solver
    if (satSolver.length() > 0) {
      BtorJNI.boolector_set_sat_solver(btor, satSolver);
    }

    // Default Options to enable multiple SAT, auto cleanup on close, incremental mode
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.swigValue(), 2);
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_AUTO_CLEANUP.swigValue(), 1);
    // Incremental needed for push/pop!
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_INCREMENTAL.swigValue(), 1);
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_SEED.swigValue(), randomSeed);
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_REWRITE_LEVEL.swigValue(), 0);

    setOptions();
  }

  /**
   * Tries to split the options string and set the options for boolector.
   *
   * @throws InvalidConfigurationException signals that the format for the options string was wrong
   *         (most likely).
   */
  private void setOptions() throws InvalidConfigurationException {
    if (furtherOptions.isEmpty()) {
      return;
    }
    MapSplitter optionSplitter =
        Splitter.on(',')
            .trimResults()
            .omitEmptyStrings()
            .withKeyValueSeparator(Splitter.on('=').limit(2).trimResults());
    ImmutableMap<String, String> furtherOptionsMap;

    try {
      furtherOptionsMap = ImmutableMap.copyOf(optionSplitter.split(furtherOptions));
    } catch (IllegalArgumentException e) {
      throw new InvalidConfigurationException(
          "Invalid Boolector option in \"" + furtherOptions + "\": " + e.getMessage(),
          e);
    }
    for (Entry<String, String> option : furtherOptionsMap.entrySet()) {
      try {
        BtorOption btorOption = BtorOption.getOption(option.getKey());
        long optionValue;
        if (btorOption == null) {
          throw new IllegalArgumentException();
        }
        optionValue = Long.parseLong(option.getValue());
        BtorJNI.boolector_set_opt(
            btor,
            btorOption.swigValue(),
            optionValue);
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      }
    }
  }

  /**
   * This method returns a new prover, that is registered in this environment. All variables are
   * shared in all registered Boolector instances(btor).
   */
  BoolectorAbstractProver<?> getNewProver(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator,
      Set<ProverOptions> pOptions) {
    return new BoolectorTheoremProver(manager, creator, btor, shutdownNotifier, pOptions);
  }

  public Long getBtor() {
    return btor;
  }

  public Long getBoolSort() {
    return BtorJNI.boolector_bool_sort(btor);
  }
}
