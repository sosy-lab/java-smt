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
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

@Options(prefix = "solver.boolector")
class BoolectorEnvironment {

  @Option(
    secure = true,
    description = "The SAT solver used by Boolector. Available are \"Lingeling\", "
        + "\"PicoSAT\" and \"MiniSAT \". Please enter the String for the Solver you "
        + "want (case insensitive). Warning: Cadical is most likely not working in "
        + "JavaSMT at this moment.")
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
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private static boolean loaded = false;

  private final long btor;

  private static final String copyright =
      "Copyright (c) 2007-2009 Robert Brummayer\n"
          + "Copyright (c) 2007-2018 Armin Biere\n"
          + "Copyright (c) 2012-2018 Aina Niemetz, Mathias Preiner\n"
          + "\n"
          + "This software is linked against Lingeling\n"
          + "Copyright (c) 2010-2018 Armin Biere\n"
          + "\n"
          + "This software is linked against PicoSAT\n"
          + "Copyright (c) 2006-2016 Armin Biere\n"
          + "\n"
          + "This software is linked against CaDiCaL\n"
          + "Copyright (c) 2016-2018 Armin Biere\n";
  // Copied from the license link on the Boolector website
  private static final String license =
      "Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the \"Software\"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:\n"
          + "\n"
          + "The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.\n"
          + "\n"
          + "THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.";

  BoolectorEnvironment(
      Configuration config,
      LogManager logger,
      @Nullable final PathCounterTemplate pBasicLogfile,
      ShutdownNotifier pShutdownNotifier,
      final int pRandomSeed)
      throws InvalidConfigurationException {

    this.logger = logger;
    this.basicLogfile = pBasicLogfile;
    this.shutdownNotifier = pShutdownNotifier;
    this.randomSeed = pRandomSeed;

    try {
      NativeLibraries.loadLibrary("boolector");
    } catch (UnsatisfiedLinkError e) {
      System.err.println("Boolector library could not be loaded.");
    }

    if (!loaded && logger != null) { // Avoid logging twice.
      logger.log(Level.WARNING, copyright + license);
    }

    btor = BtorJNI.boolector_new();
    config.inject(this);
    // Setting SAT Solver
    if (satSolver.length() > 0) {
      if (satSolver.toLowerCase() == "cadical") {
        // cadical can't be used with incremental mode, maybe this will change in the future
        System.out.println("CaDiCal is not useable with JavaSMT at this moment.");
      } else {
        BtorJNI.boolector_set_sat_solver(btor, satSolver);
      }
    }

    // Default Options to enable multiple SAT, auto cleanup on close, incremental mode
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.swigValue(), 2);
    // Auto memory clean after closing
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_AUTO_CLEANUP.swigValue(), 1);
    // Incremental needed for push/pop!
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_INCREMENTAL.swigValue(), 1);
    // Sets randomseed accordingly
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_SEED.swigValue(), randomSeed);
    // Dump in SMT-LIB2 Format
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_OUTPUT_FORMAT.swigValue(), 2);

    setOptions();
    startLogging();
    loaded = true;
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

  private void startLogging() {
    if (basicLogfile != null) {
      String filename = basicLogfile.getFreshPath().toAbsolutePath().toString();
      BtorJNI.boolector_set_trapi(btor, filename);
    }
  }
}
