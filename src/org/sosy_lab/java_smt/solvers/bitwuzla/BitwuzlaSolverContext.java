/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableMap;
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class BitwuzlaSolverContext extends AbstractSolverContext {

  enum SatSolver {
    LINGELING,
    PICOSAT,
    MINISAT,
    CMS,
    CADICAL,
    GIMSATUL,
    KISSAT
  }

  @Options(prefix = "solver.bitwuzla")
  private static class BitwuzlaSettings {

    @Option(secure = true, description = "The SAT solver used by Bitwuzla.")
    private BitwuzlaSolverContext.SatSolver satSolver = BitwuzlaSolverContext.SatSolver.CADICAL;

    @Option(
        secure = true,
        description =
            // TODO:
            "Further options for Boolector in addition to the default options. "
                + "Format:  \"Optionname=value\" with ’,’ to seperate options. "
                + "Optionname and value can be found in BtorOption or Boolector C Api."
                + "Example: \"BTOR_OPT_MODEL_GEN=2,BTOR_OPT_INCREMENTAL=1\".")
    private String furtherOptions = "";

    BitwuzlaSettings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }
  }

  private final BitwuzlaFormulaManager manager;
  private final BitwuzlaFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private boolean closed = false;
  private final AtomicBoolean isAnyStackAlive = new AtomicBoolean(false);

  BitwuzlaSolverContext(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pManager);
    manager = pManager;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
  }

  /**
   * Get version information out of the solver.
   *
   * <p>In most cases, the version contains the name of the solver followed by some numbers and
   * additional info about the version, e.g., "SMTInterpol 2.5-12-g3d15a15c".
   */
  @Override
  public String getVersion() {
    return "Bitwuzla " + bitwuzlaJNI.bitwuzla_version();
  }

  /**
   * Get solver name (MATHSAT5/Z3/etc...).
   *
   * <p>This is an uppercase String matching the enum identifier from {@link Solvers}
   */
  @Override
  public Solvers getSolverName() {
    return Solvers.BITWUZLA;
  }

  /**
   * Close the solver context.
   *
   * <p>After calling this method, further access to any object that had been returned from this
   * context is not wanted, i.e., it depends on the solver. Java-based solvers might wait for the
   * next garbage collection with any cleanup operation. Native solvers might even reference invalid
   * memory and cause segmentation faults.
   *
   * <p>Necessary for the solvers implemented in native code, frees the associated memory.
   */
  @Override
  public void close() {
    if (!closed) {
      closed = true;
      bitwuzlaJNI.bitwuzla_delete(creator.getEnv());
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new BitwuzlaTheoremProver(
        manager, creator, creator.getEnv(), shutdownNotifier, options, isAnyStackAlive);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pF) {
    throw new UnsupportedOperationException("Bitwuzla does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    // TODO: Is this true?
    throw new UnsupportedOperationException("Bitwuzla does not support optimization");
  }

  /**
   * Whether the solver supports solving under some given assumptions (with all corresponding
   * features) by itself, i.e., whether {@link ProverEnvironment#isUnsatWithAssumptions(Collection)}
   * and {@link InterpolatingProverEnvironment#isUnsatWithAssumptions(Collection)} are fully
   * implemented.
   *
   * <p>Otherwise, i.e., if this method returns {@code false}, the solver does not need to support
   * this feature and may simply {@code throw UnsupportedOperationException} in the respective
   * methods. This class will wrap the prover environments and provide an implementation of the
   * feature.
   *
   * <p>This method is expected to always return the same value. Otherwise, the behavior of this
   * class is undefined.
   */
  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }

  private static void setOptions(
      Configuration config, PathCounterTemplate solverLogfile, long randomSeed, long bitwuzla)
      throws InvalidConfigurationException {
    BitwuzlaSettings settings = new BitwuzlaSettings(config);

    Preconditions.checkNotNull(settings.satSolver);

    long options = bitwuzlaJNI.bitwuzla_options_new();

    bitwuzlaJNI.bitwuzla_set_option_mode(
        options,
        BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(),
        settings.satSolver.name().toLowerCase(Locale.getDefault()));
    // Default Options to enable multiple SAT, auto cleanup on close, incremental mode
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 2);
    // TODO: Not available in Bitwzula?
    //    BitwuzlaJNI.bitwuzla_set_option(bitwuzla,
    // SWIG_BitwuzlaOption.BTOR_OPT_AUTO_CLEANUP.getValue(), 1);
    // Incremental is always enabled.
    // Sets randomseed accordingly
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_SEED.swigValue(), randomSeed);
    // Stop Bitwuzla from rewriting formulas in outputs
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_REWRITE_LEVEL.swigValue(), 0);

    setFurtherOptions(bitwuzla, settings.furtherOptions);
    // TODO: This seems to be setting a logfile. Perhaps the SWIG _IO_FILE could be used instead?
    //    if (solverLogfile != null) {
    //      String filename = solverLogfile.getFreshPath().toAbsolutePath().toString();
    //      BtorJNI.boolector_set_trapi(bitwuzla, filename);
    //    }
  }

  /**
   * Set more options for Bitwuzla.
   *
   * @param bitwuzla solver instance.
   * @param pFurtherOptions String to be parsed with options to be set.
   * @throws InvalidConfigurationException signals that the format of the option string is wrong or
   *     an invalid option is used.
   */

  // TODO: Copied from Boolector, needs to be tested.
  private static void setFurtherOptions(long bitwuzla, String pFurtherOptions)
      throws InvalidConfigurationException {
    MapSplitter optionSplitter =
        Splitter.on(',')
            .trimResults()
            .omitEmptyStrings()
            .withKeyValueSeparator(Splitter.on('=').limit(2).trimResults());
    ImmutableMap<String, String> furtherOptionsMap;

    try {
      furtherOptionsMap = ImmutableMap.copyOf(optionSplitter.split(pFurtherOptions));
    } catch (IllegalArgumentException e) {
      throw new InvalidConfigurationException(
          "Invalid Bitwuzla option in \"" + pFurtherOptions + "\": " + e.getMessage(), e);
    }
    for (Map.Entry<String, String> option : furtherOptionsMap.entrySet()) {
      try {
        Class<?> optionClass = BitwuzlaOption.class;
        Field optionField = optionClass.getField(option.getKey());
        // Get the value of the public fields
        BitwuzlaOption value = (BitwuzlaOption) optionField.get(null);
        long optionValue = Long.parseLong(option.getValue());
        bitwuzlaJNI.bitwuzla_set_option(bitwuzla, value.swigValue(), optionValue);
      } catch (java.lang.NoSuchFieldException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      } catch (IllegalAccessException pE) {
        throw new RuntimeException("Problem with access to BitwuzlaOption Field", pE);
      }
    }
  }
}
