// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.BV_SOLVER;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.DBG_CHECK_MODEL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.DBG_CHECK_UNSAT_CORE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.DBG_PP_NODE_THRESH;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.DBG_RW_NODE_THRESH;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.LOGLEVEL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.MEMORY_LIMIT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.NUM_OPTS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_CONTRADICTING_ANDS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_ELIM_BV_EXTRACTS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_EMBEDDED_CONSTR;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_FLATTEN_AND;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_NORMALIZE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_NORMALIZE_SHARE_AWARE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_SKELETON_PREPROC;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_VARIABLE_SUBST;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_VARIABLE_SUBST_NORM_BV_INEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_VARIABLE_SUBST_NORM_DISEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PP_VARIABLE_SUBST_NORM_EQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PREPROCESS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PRODUCE_MODELS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PRODUCE_UNSAT_ASSUMPTIONS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PRODUCE_UNSAT_CORES;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_CONST_BITS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_INFER_INEQ_BOUNDS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_NORMALIZE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_NPROPS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_NUPDATES;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_OPT_LT_CONCAT_SEXT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_PATH_SEL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_PROB_RANDOM_INPUT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_PROB_USE_INV_VALUE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.PROP_SEXT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.REWRITE_LEVEL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.SAT_SOLVER;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.SEED;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.TIME_LIMIT_PER;
import static org.sosy_lab.java_smt.solvers.bitwuzla.api.Option.VERBOSITY;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.BitwuzlaNative;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Option;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;

public final class BitwuzlaSolverContext extends AbstractSolverContext {

  @org.sosy_lab.common.configuration.Options(prefix = "solver.bitwuzla")
  public static class BitwuzlaSettings {

    enum SatSolver {
      LINGELING,
      CMS,
      CADICAL,
      KISSAT
    }

    @org.sosy_lab.common.configuration.Option(
        secure = true,
        description = "The SAT solver used by Bitwuzla.")
    private SatSolver satSolver = SatSolver.CADICAL;

    @org.sosy_lab.common.configuration.Option(
        secure = true,
        description =
            "Further options for Bitwuzla in addition to the default options. "
                + "Format:  \"option_name=value\" with ’,’ to separate options. "
                + "Option names and values can be found in the Bitwuzla documentation online: "
                + "https://bitwuzla.github.io/docs/cpp/enums/option.html#_CPPv4N8bitwuzla6OptionE "
                + "Example: \"PRODUCE_MODELS=2,SAT_SOLVER=kissat\".")
    private String furtherOptions = "";

    protected SatSolver getSatSolver() {
      return satSolver;
    }

    protected String getFurtherOptions() {
      return furtherOptions;
    }

    BitwuzlaSettings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }
  }

  private final BitwuzlaFormulaManager manager;
  private final BitwuzlaFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;

  private final Options solverOptions;

  private boolean closed = false;

  BitwuzlaSolverContext(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Options pOptions) {
    super(pManager);
    manager = pManager;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    solverOptions = pOptions;
  }

  @SuppressWarnings("unused")
  public static BitwuzlaSolverContext create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {
    loadLibrary(pLoader);

    TermManager termManager = new TermManager();
    Options solverOptions = buildBitwuzlaOptions(new BitwuzlaSettings(config), randomSeed);

    BitwuzlaFormulaCreator creator = new BitwuzlaFormulaCreator(termManager);
    BitwuzlaUFManager functionTheory = new BitwuzlaUFManager(creator);
    BitwuzlaBooleanFormulaManager booleanTheory = new BitwuzlaBooleanFormulaManager(creator);
    BitwuzlaBitvectorFormulaManager bitvectorTheory =
        new BitwuzlaBitvectorFormulaManager(creator, booleanTheory);
    BitwuzlaQuantifiedFormulaManager quantifierTheory =
        new BitwuzlaQuantifiedFormulaManager(creator);
    BitwuzlaFloatingPointManager floatingPointTheory =
        new BitwuzlaFloatingPointManager(creator, pFloatingPointRoundingMode);
    BitwuzlaArrayFormulaManager arrayTheory = new BitwuzlaArrayFormulaManager(creator);
    BitwuzlaFormulaManager manager =
        new BitwuzlaFormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            bitvectorTheory,
            quantifierTheory,
            floatingPointTheory,
            arrayTheory,
            solverOptions);

    return new BitwuzlaSolverContext(manager, creator, pShutdownNotifier, solverOptions);
  }

  @VisibleForTesting
  static void loadLibrary(Consumer<String> pLoader) {
    loadLibrariesWithFallback(
        pLoader, ImmutableList.of("bitwuzlaj"), ImmutableList.of("libbitwuzlaj"));
  }

  /**
   * Set more options for Bitwuzla.
   *
   * @param pOptions current Bitwuzla options
   * @param pFurtherOptions String to be parsed with options to be set.
   * @throws InvalidConfigurationException signals that the format of the option string is wrong or
   *     an invalid option is used.
   */
  private static Options setFurtherOptions(Options pOptions, String pFurtherOptions)
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
      String optionName = option.getKey();
      String optionValue = option.getValue();
      Option bitwuzlaOption = getBitwuzlaOptByString(optionName);
      try {
        if (pOptions.is_numeric(bitwuzlaOption)) {
          pOptions.set(bitwuzlaOption, Integer.parseInt(optionValue));
        } else {
          pOptions.set(bitwuzlaOption, option.getValue());
        }
      } catch (NumberFormatException e) {
        throw new InvalidConfigurationException(
            "Option "
                + bitwuzlaOption
                + " needs a numeric "
                + "value as option value, but you entered "
                + optionValue);
      }
    }
    return pOptions;
  }

  private static Options buildBitwuzlaOptions(BitwuzlaSettings settings, long randomSeed)
      throws InvalidConfigurationException {
    Preconditions.checkNotNull(settings.getSatSolver());

    Options options = new Options();
    options.set(SAT_SOLVER, settings.getSatSolver().name().toLowerCase(Locale.getDefault()));
    options.set(SEED, (int) randomSeed);
    options.set(REWRITE_LEVEL, 0); // Stop Bitwuzla from rewriting formulas in outputs

    return setFurtherOptions(options, settings.getFurtherOptions());
  }

  /**
   * Get version information out of the solver.
   *
   * <p>In most cases, the version contains the name of the solver followed by some numbers and
   * additional info about the version, e.g., "SMTInterpol 2.5-12-g3d15a15c".
   */
  @Override
  public String getVersion() {
    return "Bitwuzla " + BitwuzlaNative.version();
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
      creator.getTermManager().delete();
      closed = true;
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");

    return new BitwuzlaTheoremProver(manager, creator, shutdownNotifier, options, solverOptions);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pF) {
    throw new UnsupportedOperationException("Bitwuzla does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
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

  public static Option getBitwuzlaOptByString(String optionName) {
    switch (optionName) {
      case "LOGLEVEL":
        return LOGLEVEL;
      case "PRODUCE_MODELS":
        return PRODUCE_MODELS;
      case "PRODUCE_UNSAT_ASSUMPTIONS":
        return PRODUCE_UNSAT_ASSUMPTIONS;
      case "PRODUCE_UNSAT_CORES":
        return PRODUCE_UNSAT_CORES;
      case "SEED":
        return SEED;
      case "VERBOSITY":
        return VERBOSITY;
      case "TIME_LIMIT_PER":
        return TIME_LIMIT_PER;
      case "MEMORY_LIMIT":
        return MEMORY_LIMIT;
      case "BV_SOLVER":
        return BV_SOLVER;
      case "REWRITE_LEVEL":
        return REWRITE_LEVEL;
      case "SAT_SOLVER":
        return SAT_SOLVER;
      case "PROP_CONST_BITS":
        return PROP_CONST_BITS;
      case "PROP_INFER_INEQ_BOUNDS":
        return PROP_INFER_INEQ_BOUNDS;
      case "PROP_NPROPS":
        return PROP_NPROPS;
      case "PROP_NUPDATES":
        return PROP_NUPDATES;
      case "PROP_OPT_LT_CONCAT_SEXT":
        return PROP_OPT_LT_CONCAT_SEXT;
      case "PROP_PATH_SEL":
        return PROP_PATH_SEL;
      case "PROP_PROB_RANDOM_INPUT":
        return PROP_PROB_RANDOM_INPUT;
      case "PROP_PROB_USE_INV_VALUE":
        return PROP_PROB_USE_INV_VALUE;
      case "PROP_SEXT":
        return PROP_SEXT;
      case "PROP_NORMALIZE":
        return PROP_NORMALIZE;
      case "PREPROCESS":
        return PREPROCESS;
      case "PP_CONTRADICTING_ANDS":
        return PP_CONTRADICTING_ANDS;
      case "PP_ELIM_BV_EXTRACTS":
        return PP_ELIM_BV_EXTRACTS;
      case "PP_EMBEDDED_CONSTR":
        return PP_EMBEDDED_CONSTR;
      case "PP_FLATTEN_AND":
        return PP_FLATTEN_AND;
      case "PP_NORMALIZE":
        return PP_NORMALIZE;
      case "PP_NORMALIZE_SHARE_AWARE":
        return PP_NORMALIZE_SHARE_AWARE;
      case "PP_SKELETON_PREPROC":
        return PP_SKELETON_PREPROC;
      case "PP_VARIABLE_SUBST":
        return PP_VARIABLE_SUBST;
      case "PP_VARIABLE_SUBST_NORM_EQ":
        return PP_VARIABLE_SUBST_NORM_EQ;
      case "PP_VARIABLE_SUBST_NORM_DISEQ":
        return PP_VARIABLE_SUBST_NORM_DISEQ;
      case "PP_VARIABLE_SUBST_NORM_BV_INEQ":
        return PP_VARIABLE_SUBST_NORM_BV_INEQ;
      case "DBG_RW_NODE_THRESH":
        return DBG_RW_NODE_THRESH;
      case "DBG_PP_NODE_THRESH":
        return DBG_PP_NODE_THRESH;
      case "DBG_CHECK_MODEL":
        return DBG_CHECK_MODEL;
      case "DBG_CHECK_UNSAT_CORE":
        return DBG_CHECK_UNSAT_CORE;
      case "NUM_OPTS":
        return NUM_OPTS;
      default:
        // Possibly new option that needs to be entered into the switch case
        throw new IllegalArgumentException(
            "Unknown option: " + optionName + ". Please use the C++ " + "options of Bitwuzla.");
    }
  }
}
