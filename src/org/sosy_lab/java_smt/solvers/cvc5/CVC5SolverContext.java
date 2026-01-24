// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import io.github.cvc5.CVC5ApiRecoverableException;
import io.github.cvc5.Context;
import io.github.cvc5.Solver;
import io.github.cvc5.TermManager;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC5SolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.cvc5")
  private static final class CVC5Settings {

    @Option(
        secure = true,
        description = "apply additional validation checks for interpolation results")
    private boolean validateInterpolants = false;

    @Option(
        secure = true,
        description =
            "Further options that will be passed to CVC5 in addition to the default options. "
                + "Format is 'key1=value1,key2=value2'")
    private String furtherOptions = "";

    private final ImmutableMap<String, String> furtherOptionsMap;

    private CVC5Settings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);

      MapSplitter optionSplitter =
          Splitter.on(',')
              .trimResults()
              .omitEmptyStrings()
              .withKeyValueSeparator(Splitter.on('=').limit(2).trimResults());

      try {
        furtherOptionsMap = ImmutableMap.copyOf(optionSplitter.split(furtherOptions));
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(
            "Invalid CVC5 option in \"" + furtherOptions + "\": " + e.getMessage(), e);
      }
    }
  }

  // creator is final, except after closing, then null.
  private CVC5FormulaCreator creator;
  private final Solver solver;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;
  private final CVC5Settings settings;
  private boolean closed = false;

  /** Counts the number of (open) CVC5 solver contexts. * */
  private static int instances = 0;

  private CVC5SolverContext(
      CVC5FormulaCreator pCreator,
      CVC5FormulaManager pManager,
      ShutdownNotifier pShutdownNotifier,
      Solver pSolver,
      int pRandomSeed,
      CVC5Settings pSettings) {
    super(pManager);
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
    solver = pSolver;
    settings = pSettings;
  }

  @VisibleForTesting
  static void loadLibrary(Consumer<String> pLoader) {
    loadLibrariesWithFallback(pLoader, ImmutableList.of("cvc5jni"), ImmutableList.of("libcvc5jni"));

    // disable CVC5's own loading mechanism,
    // see io.github.cvc5.Util#loadLibraries and https://github.com/cvc5/cvc5/pull/9047
    System.setProperty("cvc5.skipLibraryLoad", "true");
  }

  @SuppressWarnings({"unused", "resource"})
  public static SolverContext create(
      LogManager pLogger,
      Configuration pConfig,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {

    synchronized (CVC5SolverContext.class) {
      // Increase counter *before* any CVC5 objects are created
      instances++;
    }

    CVC5Settings settings = new CVC5Settings(pConfig);

    loadLibrary(pLoader);

    // The TermManager is the central class for creating expressions/terms/formulae.
    // We keep this instance available until the whole context is closed.
    TermManager termManager = new TermManager();

    // Create a new solver instance
    // We'll use this instance in some of the formula managers for simplifying terms and declaring
    // datatypes. The actual solving is done on a different instance that is created by
    // newProverEnvironment()
    Solver newSolver = new Solver(termManager);

    try {
      setSolverOptions(newSolver, randomSeed, settings.furtherOptionsMap);
    } catch (CVC5ApiRecoverableException e) { // we do not want to recover after invalid options.
      throw new InvalidConfigurationException(e.getMessage(), e);
    }

    CVC5FormulaCreator pCreator = new CVC5FormulaCreator(termManager, newSolver);

    // Create managers
    CVC5UFManager functionTheory = new CVC5UFManager(pCreator);
    CVC5BooleanFormulaManager booleanTheory = new CVC5BooleanFormulaManager(pCreator);
    CVC5IntegerFormulaManager integerTheory =
        new CVC5IntegerFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5RationalFormulaManager rationalTheory =
        new CVC5RationalFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5BitvectorFormulaManager bitvectorTheory =
        new CVC5BitvectorFormulaManager(pCreator, booleanTheory);
    CVC5FloatingPointFormulaManager fpTheory =
        new CVC5FloatingPointFormulaManager(pCreator, pFloatingPointRoundingMode);
    CVC5QuantifiedFormulaManager qfTheory = new CVC5QuantifiedFormulaManager(pCreator, newSolver);
    CVC5ArrayFormulaManager arrayTheory = new CVC5ArrayFormulaManager(pCreator);
    CVC5SLFormulaManager slTheory = new CVC5SLFormulaManager(pCreator);
    CVC5StringFormulaManager strTheory = new CVC5StringFormulaManager(pCreator);
    CVC5EnumerationFormulaManager enumTheory = new CVC5EnumerationFormulaManager(pCreator);
    CVC5FormulaManager manager =
        new CVC5FormulaManager(
            pCreator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            fpTheory,
            qfTheory,
            arrayTheory,
            slTheory,
            strTheory,
            enumTheory);

    return new CVC5SolverContext(
        pCreator, manager, pShutdownNotifier, newSolver, randomSeed, settings);
  }

  /**
   * Set common options for a CVC5 solver.
   *
   * @throws CVC5ApiRecoverableException from native code.
   */
  static void setSolverOptions(
      Solver pSolver, int randomSeed, ImmutableMap<String, String> furtherOptions)
      throws CVC5ApiRecoverableException {
    pSolver.setOption("seed", String.valueOf(randomSeed));
    pSolver.setOption("output-language", "smtlib2");

    // Enable support for arbitrary size floating-point formats
    pSolver.setOption("fp-exp", "true");

    for (Entry<String, String> option : furtherOptions.entrySet()) {
      pSolver.setOption(option.getKey(), option.getValue());
    }
  }

  @Override
  public String getVersion() {
    return "CVC5 " + solver.getVersion();
  }

  @SuppressFBWarnings(
      value = "ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD",
      justification = "Static reference counter guarded by class-level synchronization")
  @Override
  public void close() {
    if (!closed) {
      synchronized (CVC5SolverContext.class) {
        if (instances == 1) {
          // Delete all solver objects if we're closing the last instance
          Context.deletePointers();
        } else {
          // Otherwise, only delete the Solver, but keep the TermManager and all other objects
          // Closing the TermManager here will cause a segfault later
          solver.deletePointer();
        }
        instances--;
      }
      creator = null;
      closed = true;
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC5;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new CVC5TheoremProver(
        creator,
        shutdownNotifier,
        randomSeed,
        ImmutableSet.copyOf(pOptions),
        getFormulaManager(),
        settings.furtherOptionsMap);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pOptions) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new CVC5InterpolatingProver(
        creator,
        shutdownNotifier,
        randomSeed,
        ImmutableSet.copyOf(pOptions),
        getFormulaManager(),
        settings.furtherOptionsMap,
        settings.validateInterpolants);
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC5 does not support optimization");
  }
}
