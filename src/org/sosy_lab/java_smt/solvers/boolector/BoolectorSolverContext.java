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

import com.google.common.base.Preconditions;
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
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackTheoremProver;

public final class BoolectorSolverContext extends AbstractSolverContext {

  enum SatSolver {
    LINGELING,
    PICOSAT,
    MINISAT,
    CADICAL
  }

  @Options(prefix = "solver.boolector")
  private static class BoolectorSettings {

    @Option(secure = true, description = "The SAT solver used by Boolector.")
    private SatSolver satSolver = SatSolver.PICOSAT;

    @Option(
        secure = true,
        description =
            "Further options for Boolector in addition to the default options. "
                + "Format:  \"Optionname=value\" with ’,’ to seperate options. "
                + "Optionname and value can be found in BtorOption or Boolector C Api."
                + "Example: \"BTOR_OPT_MODEL_GEN=2,BTOR_OPT_INCREMENTAL=1\".")
    private String furtherOptions = "";

    BoolectorSettings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }
  }

  private final BoolectorFormulaManager manager;
  private final BoolectorFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private boolean closed = false;

  protected BoolectorSolverContext(
      BoolectorFormulaManager pManager,
      BoolectorFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pManager);
    manager = pManager;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
  }

  public static BoolectorSolverContext create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed)
      throws InvalidConfigurationException {

    NativeLibraries.loadLibrary("boolector");
    final long btor = BtorJNI.boolector_new();
    setOptions(config, solverLogfile, randomSeed, btor);

    BoolectorFormulaCreator creator = new BoolectorFormulaCreator(btor);
    BoolectorUFManager functionTheory = new BoolectorUFManager(creator);
    BoolectorBooleanFormulaManager booleanTheory = new BoolectorBooleanFormulaManager(creator);
    BoolectorBitvectorFormulaManager bitvectorTheory =
        new BoolectorBitvectorFormulaManager(creator);
    BoolectorQuantifiedFormulaManager quantifierTheory =
        new BoolectorQuantifiedFormulaManager(creator);
    BoolectorArrayFormulaManager arrayTheory = new BoolectorArrayFormulaManager(creator);
    BoolectorFormulaManager manager =
        new BoolectorFormulaManager(
            creator, functionTheory, booleanTheory, bitvectorTheory, quantifierTheory, arrayTheory);
    return new BoolectorSolverContext(manager, creator, pShutdownNotifier);
  }

  @Override
  public String getVersion() {
    return BtorJNI.boolector_version(creator.getEnv());
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.BOOLECTOR;
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      BtorJNI.boolector_delete(creator.getEnv());
    }
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new ReusableStackTheoremProver(
        new BoolectorTheoremProver(manager, creator, creator.getEnv(), shutdownNotifier, pOptions));
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Boolector does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Boolector does not support optimization");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }

  /** set basic options for running Boolector. */
  private static void setOptions(
      Configuration config, PathCounterTemplate solverLogfile, long randomSeed, long btor)
      throws InvalidConfigurationException {
    BoolectorSettings settings = new BoolectorSettings(config);

    Preconditions.checkNotNull(settings.satSolver);
    // TODO implement non-incremental stack-handling in the TheoremProver.
    Preconditions.checkArgument(
        settings.satSolver != SatSolver.CADICAL,
        "CaDiCal is not usable with JavaSMT, because it does not support incremental mode.");
    BtorJNI.boolector_set_sat_solver(btor, settings.satSolver.name());
    // Default Options to enable multiple SAT, auto cleanup on close, incremental mode
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.getValue(), 2);
    // Auto memory clean after closing
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_AUTO_CLEANUP.getValue(), 1);
    // Incremental needed for push/pop!
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_INCREMENTAL.getValue(), 1);
    // Sets randomseed accordingly
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_SEED.getValue(), randomSeed);
    // Dump in SMT-LIB2 Format
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_OUTPUT_FORMAT.getValue(), 2);

    setFurtherOptions(btor, settings.furtherOptions);

    if (solverLogfile != null) {
      String filename = solverLogfile.getFreshPath().toAbsolutePath().toString();
      BtorJNI.boolector_set_trapi(btor, filename);
    }
  }

  /**
   * Set more options for Boolector.
   *
   * @param btor solver instance.
   * @param pFurtherOptions String to be parsed with options to be set.
   * @throws InvalidConfigurationException signals that the format of the option string is wrong or
   *     an invalid option is used.
   */
  private static void setFurtherOptions(long btor, String pFurtherOptions)
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
          "Invalid Boolector option in \"" + pFurtherOptions + "\": " + e.getMessage(), e);
    }
    for (Entry<String, String> option : furtherOptionsMap.entrySet()) {
      try {
        BtorOption btorOption = BtorOption.valueOf(option.getKey());
        long optionValue = Long.parseLong(option.getValue());
        BtorJNI.boolector_set_opt(btor, btorOption.getValue(), optionValue);
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      }
    }
  }
}
