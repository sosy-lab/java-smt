// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
                + "Option names and values can be found in the Bitwuzla documentation online:"
                + "https://bitwuzla.github.io/docs/cpp/enums/option.html#_CPPv4N8bitwuzla6OptionE"
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
    pLoader.accept("bitwuzlaJNI");

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
      try {
        Class<?> optionClass = Option.class;
        Field optionField = optionClass.getField(option.getKey());
        // Get the value of the public fields
        Option value = (Option) optionField.get(null);
        if (pOptions.is_numeric(value)) {
          pOptions.set(value, Integer.parseInt(option.getValue()));
        } else {
          pOptions.set(value, option.getValue());
        }
      } catch (java.lang.NoSuchFieldException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      } catch (IllegalAccessException pE) {
        throw new RuntimeException("Problem with access to BitwuzlaOption Field", pE);
      }
    }
    return pOptions;
  }

  private static Options buildBitwuzlaOptions(BitwuzlaSettings settings, long randomSeed)
      throws InvalidConfigurationException {
    Preconditions.checkNotNull(settings.getSatSolver());

    Options options = new Options();
    options.set(Option.SAT_SOLVER, settings.getSatSolver().name().toLowerCase(Locale.getDefault()));
    options.set(Option.SEED, (int) randomSeed);
    options.set(Option.REWRITE_LEVEL, 0); // Stop Bitwuzla from rewriting formulas in outputs

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
}
