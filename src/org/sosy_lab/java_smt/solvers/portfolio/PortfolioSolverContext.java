/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class PortfolioSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.portfolio")
  private static class PortfolioSettings {

    @Option(
        secure = true,
        description =
            "Further options for solvers additional to the default ones. Usage: "
                + "list wanted solvers seperated by a single comma ','. "
                + "Example: \"BOOLECTOR,Z3,YICES2\"")
    private String solvers = "";

    private final List<Solvers> solversList;

    PortfolioSettings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
      ImmutableList.Builder<Solvers> builder = ImmutableList.builder();
      // Replace all whitespaces and invisible chars with nothing
      for (String solverName : solvers.replaceAll("\\s+", "").split(",")) {
        if (solverName.isEmpty()) {
          throw new InvalidConfigurationException(
              "You need to specify at least one solvers for " + "portfolio mode");
        }
        Solvers solver = Solvers.valueOf(sanitizeSolverNames(solverName.toUpperCase()));
        builder.add(solver);
      }
      solversList = builder.build();
    }

    public List<Solvers> getSolversList() {
      return solversList;
    }

    private String sanitizeSolverNames(final String upperCaseSolverName)
        throws InvalidConfigurationException {
      if (upperCaseSolverName.equals("PORTFOLIO")) {
        throw new InvalidConfigurationException("You can't nest the portfolio solver.");
      }
      if (Arrays.stream(Solvers.values()).anyMatch(s -> s.toString().equals(upperCaseSolverName))) {
        return upperCaseSolverName;
      }
      String sanitizedName;
      switch (upperCaseSolverName) {
        case "MATHSAT":
          sanitizedName = upperCaseSolverName + "5";
          break;
        case "OPENSMT2":
          sanitizedName = "OPENSMT";
          break;
        case "YICES":
          sanitizedName = "YICES2";
          break;
        default:
          throw new InvalidConfigurationException(
              "Solver name "
                  + upperCaseSolverName
                  + " "
                  + "unknown, try one of the following: "
                  + Arrays.stream(Solvers.values())
                      .map(Enum::toString)
                      .collect(Collectors.joining(", ")));
      }
      return sanitizedName;
    }
  }

  private final Map<Solvers, SolverContext> solversWithContexts;
  private final LogManager logger;
  private final PortfolioFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private boolean closed = false;

  PortfolioSolverContext(
      Map<Solvers, SolverContext> pSolversWithContexts,
      PortfolioFormulaManager pManager,
      PortfolioFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(pManager);
    solversWithContexts = pSolversWithContexts;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    logger = pLogger;
  }

  // TODO: provide constructor with all arguments as maps as well.
  // TODO: logfiles would be accessed concurrently, which is not good ;D
  public static PortfolioSolverContext create(
      Configuration config,
      LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {
    PortfolioSettings settings = new PortfolioSettings(config);
    List<Solvers> solvers = settings.getSolversList();
    if (solvers.size() != ImmutableSet.copyOf(solvers).size()) {
      throw new InvalidConfigurationException("You can't choose a solver twice in portfolio mode");
    }
    ImmutableMap.Builder<Solvers, SolverContext> solversWithContextsBuilder =
        ImmutableMap.builder();
    for (Solvers solver : solvers) {
      solversWithContextsBuilder.put(
          solver,
          SolverContextFactory.createSolverContext(
              config, logger, pShutdownNotifier, solver, pLoader));
    }
    Map<Solvers, SolverContext> solversWithContexts = solversWithContextsBuilder.buildOrThrow();

    ImmutableMap.Builder<Solvers, FormulaManager> solversToManagersBuilder = ImmutableMap.builder();
    ImmutableMap.Builder<Solvers, FormulaCreator<?, ?, ?, ?>> solversToCreatorsBuilder =
        ImmutableMap.builder();
    for (Entry<Solvers, SolverContext> solverAndContext : solversWithContexts.entrySet()) {
      FormulaManager manager = solverAndContext.getValue().getFormulaManager();
      FormulaCreator<?, ?, ?, ?> creator =
          ((AbstractFormulaManager<?, ?, ?, ?>) manager).getFormulaCreator();
      solversToManagersBuilder.put(solverAndContext.getKey(), manager);
      solversToCreatorsBuilder.put(solverAndContext.getKey(), creator);
    }

    Map<Solvers, FormulaManager> solversToManagers = solversToManagersBuilder.buildOrThrow();

    PortfolioFormulaCreator creator =
        new PortfolioFormulaCreator(solversToCreatorsBuilder.buildOrThrow(), solversToManagers);
    PortfolioUFManager ufMgr = new PortfolioUFManager(creator);
    PortfolioBooleanFormulaManager booleanManager = new PortfolioBooleanFormulaManager(creator);
    PortfolioIntegerFormulaManager integerManager =
        new PortfolioIntegerFormulaManager(creator, pNonLinearArithmetic);
    PortfolioRationalFormulaManager rationalManager =
        new PortfolioRationalFormulaManager(creator, pNonLinearArithmetic);
    PortfolioBitvectorFormulaManager bitvectorManager =
        new PortfolioBitvectorFormulaManager(creator, booleanManager);
    new PortfolioBitvectorFormulaManager(creator, booleanManager);
    PortfolioFloatingPointFormulaManager floatingPointManager =
        new PortfolioFloatingPointFormulaManager(creator, pFloatingPointRoundingMode);
    PortfolioQuantifiedFormulaManager quantifiedManager =
        new PortfolioQuantifiedFormulaManager(creator);
    PortfolioArrayFormulaManager arrayManager = new PortfolioArrayFormulaManager(creator);
    PortfolioSLFormulaManager slManager = new PortfolioSLFormulaManager(creator);
    PortfolioStringFormulaManager strManager = new PortfolioStringFormulaManager(creator);
    PortfolioEnumerationFormulaManager enumerationManager =
        new PortfolioEnumerationFormulaManager(creator);

    PortfolioFormulaManager manager =
        new PortfolioFormulaManager(
            solversToManagers,
            creator,
            ufMgr,
            booleanManager,
            integerManager,
            rationalManager,
            bitvectorManager,
            floatingPointManager,
            quantifiedManager,
            arrayManager,
            slManager,
            strManager,
            enumerationManager);

    return new PortfolioSolverContext(
        solversWithContexts, manager, creator, pShutdownNotifier, logger);
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return new PortfolioTheoremProver(
        options, solversWithContexts, creator, shutdownNotifier, logger);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }

  @Override
  public SolverContext copyWithNewShutdownNotifier(ShutdownNotifier pShutdownNotifier) {
    throw new UnsupportedOperationException();
  }

  @Override
  public String getVersion() {
    return solversWithContexts.entrySet().stream()
        .map(e -> e.getKey().toString() + ": " + e.getValue().getVersion())
        .collect(Collectors.joining("\n"));
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.PORTFOLIO;
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      for (SolverContext solver : solversWithContexts.values()) {
        solver.close();
      }
      solversWithContexts.clear();
    }
  }
}
