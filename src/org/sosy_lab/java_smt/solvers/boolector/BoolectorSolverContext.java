// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableMap;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class BoolectorSolverContext extends AbstractSolverContext {

  enum SatSolver {
    LINGELING,
    PICOSAT,
    MINISAT,
    CMS,
    CADICAL
  }

  @Options(prefix = "solver.boolector")
  private static class BoolectorSettings {

    @Option(secure = true, description = "The SAT solver used by Boolector.")
    private SatSolver satSolver = SatSolver.CADICAL;

    @Option(
        secure = true,
        description =
            "Further options for Boolector in addition to the default options. "
                + "Format:  \"Optionname=value\" with ’,’ to separate options. "
                + "Option names and values can be found in BtorOption or Boolector C Api. "
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
  private final AtomicBoolean isAnyStackAlive = new AtomicBoolean(false);

  BoolectorSolverContext(
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
      long randomSeed,
      Consumer<String> pLoader,
      LogManager pLogger)
      throws InvalidConfigurationException {

    pLoader.accept("boolector");

    final long btor = BtorJNI.boolector_new();
    setOptions(config, solverLogfile, randomSeed, btor);

    BoolectorFormulaCreator creator = new BoolectorFormulaCreator(btor);
    BoolectorUFManager functionTheory = new BoolectorUFManager(creator);
    BoolectorBooleanFormulaManager booleanTheory = new BoolectorBooleanFormulaManager(creator);
    BoolectorBitvectorFormulaManager bitvectorTheory =
        new BoolectorBitvectorFormulaManager(creator, booleanTheory);
    BoolectorQuantifiedFormulaManager quantifierTheory =
        new BoolectorQuantifiedFormulaManager(creator, pLogger);
    BoolectorArrayFormulaManager arrayTheory = new BoolectorArrayFormulaManager(creator);
    BoolectorFormulaManager manager =
        new BoolectorFormulaManager(
            creator, functionTheory, booleanTheory, bitvectorTheory, quantifierTheory, arrayTheory);
    return new BoolectorSolverContext(manager, creator, pShutdownNotifier);
  }

  @Override
  public String getVersion() {
    return "Boolector " + BtorJNI.boolector_version(creator.getEnv());
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.BOOLECTOR;
  }

  /**
   * Boolector returns a pre-formatted text for statistics. We might need to parse it. Example:
   *
   * <pre>
   * [btor>sat] 15 SAT calls in 0,0 seconds
   * [btor>core] 0/0/0/0 constraints 0/0/0/0 0,0 MB
   * [btor>core] 10 assumptions
   * [btor>core]
   * [btor>core]     0 max rec. RW
   * [btor>core]    67 number of expressions ever created
   * [btor>core]    67 number of final expressions
   * [btor>core] 0,01 MB allocated for nodes
   * [btor>core]  bvconst: 5 max 5
   * [btor>core]  var: 6 max 6
   * [btor>core]  slice: 6 max 6
   * [btor>core]  and: 35 max 35
   * [btor>core]  beq: 13 max 13
   * [btor>core]  ult: 2 max 2
   * [btor>core]
   * [btor>core]     0 variable substitutions
   * [btor>core]     0 uninterpreted function substitutions
   * [btor>core]     0 embedded constraint substitutions
   * [btor>core]     0 synthesized nodes rewritten
   * [btor>core]     0 linear constraint equations
   * [btor>core]     0 gaussian eliminations in linear equations
   * [btor>core]     0 eliminated sliced variables
   * [btor>core]     0 extracted skeleton constraints
   * [btor>core]     0 and normalizations
   * [btor>core]     0 add normalizations
   * [btor>core]     0 mul normalizations
   * [btor>core]     0 lambdas merged
   * [btor>core]     0 static apply propagations over lambdas
   * [btor>core]     0 static apply propagations over updates
   * [btor>core]     0 beta reductions
   * [btor>core]     0 clone calls
   * [btor>core]
   * [btor>core] rewrite rule cache
   * [btor>core]   0 cached (add)
   * [btor>core]   0 cached (get)
   * [btor>core]   0 updated
   * [btor>core]   0 removed (gc)
   * [btor>core]   0,00 MB cache
   * [btor>core]
   * [btor>core] bit blasting statistics:
   * [btor>core]        65 AIG vectors (65 max)
   * [btor>core]        35 AIG ANDs (35 max)
   * [btor>core]        12 AIG variables
   * [btor>core]        45 CNF variables
   * [btor>core]       100 CNF clauses
   * [btor>core]       236 CNF literals
   * [btor>slvfun]
   * [btor>slvfun]       0 expression evaluations
   * [btor>slvfun]       0 partial beta reductions
   * [btor>slvfun]       0 propagations
   * [btor>slvfun]       0 propagations down
   * [btor>core]
   * [btor>core] 0,0 MB
   * </pre>
   */
  @Override
  public ImmutableMap<String, String> getStatistics() {

    // get plain statistics
    final long env = creator.getEnv();
    BtorJNI.boolector_set_opt(env, BtorOption.BTOR_OPT_VERBOSITY.getValue(), 3);
    String stats = BtorJNI.boolector_print_stats_helper(env);
    BtorJNI.boolector_set_opt(env, BtorOption.BTOR_OPT_VERBOSITY.getValue(), 0);

    // then parse them into a map
    // TODO ... forget it, Boolector dumps it in human-readable form,
    // there is no simple way of converting it into a key-value-mapping.

    return ImmutableMap.of("statistics", stats);
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
    return new BoolectorTheoremProver(
        manager, creator, creator.getEnv(), shutdownNotifier, pOptions, isAnyStackAlive);
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
    BtorJNI.boolector_set_sat_solver(
        btor, settings.satSolver.name().toLowerCase(Locale.getDefault()));
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
    // Stop Boolector from rewriting formulas in outputs
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_REWRITE_LEVEL.getValue(), 0);

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
    for (Map.Entry<String, String> option : furtherOptionsMap.entrySet()) {
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
