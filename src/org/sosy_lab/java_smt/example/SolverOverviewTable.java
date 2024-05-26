// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Supplier;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This program takes all installed solvers and checks them for version, theories and features and
 * prints them to StdOut in a nice table.
 */
public class SolverOverviewTable {

  public static void main(String[] args) throws SolverException, InterruptedException {

    final List<SolverInfo> infos = new ArrayList<>();
    for (Solvers s : Solvers.values()) {
      infos.add(new SolverOverviewTable().getSolverInformation(s));
    }

    infos.sort(Comparator.comparing(SolverInfo::getName)); // alphabetical ordering

    RowBuilder rowBuilder = new RowBuilder();
    for (SolverInfo info : infos) {
      rowBuilder.addSolver(info);
    }
    System.out.println(rowBuilder);
  }

  /**
   * Checks for solver-name, version, theories and features.
   *
   * @param solver to check for information. Taken from Solvers enum only.
   * @return Information about the solver you entered or NULL if the solver is not available.
   */
  public @Nullable SolverInfo getSolverInformation(Solvers solver)
      throws SolverException, InterruptedException {

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = LogManager.createNullLogManager();
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

      String version = context.getVersion();
      String theories = String.join(", ", getTheories(context));
      String features = String.join(", ", getFeatures(context));

      return new SolverInfo(solver, version, theories, features);
    } catch (InvalidConfigurationException e) {
      // Catches missing solvers
      return new SolverInfo(solver, "NOT AVAILABLE", "", "");
    }
  }

  /**
   * Checks the solver entered for features. Features checked: Optimization, UnsatCore,
   * UnsatCoreWithAssumptions, Assumptions, AllSat, Interpolation
   *
   * @param context SolverContext you want to check for features.
   * @return String with the features of the entered solver separated by a comma. Empty if none
   *     available.
   */
  @SuppressWarnings({"CheckReturnValue", "resource"})
  private List<String> getFeatures(SolverContext context)
      throws SolverException, InterruptedException {
    List<String> features = new ArrayList<>();

    // Optimization: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      Preconditions.checkNotNull(prover);
      features.add("Optimization");
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    }

    // Interpolation: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (InterpolatingProverEnvironment<?> prover =
        context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS)) {
      Preconditions.checkNotNull(prover);
      features.add("Interpolation");
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    }

    // We don't care about the return value, just that it doesn't throw an
    // UnsupportedOperationException.
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      try {
        prover.isUnsatWithAssumptions(ImmutableList.of());
        features.add("Assumptions");
      } catch (UnsupportedOperationException e) {
        // ignore, feature is not supported.
      }
    }

    // UnsatCoreOverAssumptions: throws NullPointerException if available.
    try (ProverEnvironment prover =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      prover.unsatCoreOverAssumptions(ImmutableList.of());
      features.add("UnsatCore /w Assumption");
    } catch (UnsupportedOperationException | IllegalStateException e) {
      // ignore, feature is not supported.
    }

    // UnsatCore: throws UnsupportedOperationException if not available.
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      prover.push(context.getFormulaManager().getBooleanFormulaManager().makeFalse());
      Preconditions.checkState(prover.isUnsat());
      Preconditions.checkNotNull(prover.getUnsatCore());
      features.add("UnsatCore");
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    }

    // There is currently no good way of checking if a solver implements AllSat over our
    // implementation

    return features;
  }

  /**
   * This method checks the SolverContext entered for all its available theories and gives them back
   * as String with each theory separated by a comma.
   *
   * @param context JavaSMT SolverContext of the Solver you want to check for theories.
   * @return String of all supported theories except Booleans, separated by a comma. Empty if none
   *     available.
   */
  private List<String> getTheories(SolverContext context) {
    List<String> theories = new ArrayList<>();
    FormulaManager mgr = context.getFormulaManager();

    // Every solver has to have Bool-Theory, should we add it?
    addIfAvailable(theories, mgr::getIntegerFormulaManager, "Integer");
    addIfAvailable(theories, mgr::getBitvectorFormulaManager, "Bitvector");
    addIfAvailable(theories, mgr::getRationalFormulaManager, "Rational");
    addIfAvailable(theories, mgr::getFloatingPointFormulaManager, "Float");
    addIfAvailable(theories, mgr::getArrayFormulaManager, "Array");
    addIfAvailable(theories, mgr::getQuantifiedFormulaManager, "Quantifier");
    addIfAvailable(theories, mgr::getUFManager, "UF");
    addIfAvailable(theories, mgr::getEnumerationFormulaManager, "Enumeration");
    addIfAvailable(theories, mgr::getSLFormulaManager, "Seperation-Logic");
    addIfAvailable(theories, mgr::getStringFormulaManager, "String");

    return theories;
  }

  /**
   * Try to construct an object and add its name to the list of theories. If an object cannot be
   * constructed, we ignore it.
   *
   * @param names where to add the new name if available.
   * @param creator creates the object, allowed to fail with {@link UnsupportedOperationException}.
   * @param name the name to be added.
   */
  private void addIfAvailable(List<String> names, Supplier<Object> creator, String name) {
    try {
      if (creator.get() != null) {
        names.add(name);
      }
    } catch (UnsupportedOperationException e) {
      // ignore, theory is not supported.
    }
  }

  /** just a wrapper for some data. */
  public static class SolverInfo {
    private final Solvers solver;
    private final String solverVersion;
    private final String solverTheories;
    private final String solverFeatures;

    /**
     * Saves the information of a solver.
     *
     * @param solver Solvers enum object for a solver.
     * @param solverVersion Solver version String.
     * @param solverTheories Solver theories String.
     * @param solverFeatures Solver features String.
     */
    SolverInfo(Solvers solver, String solverVersion, String solverTheories, String solverFeatures) {
      this.solver = solver;
      this.solverVersion = solverVersion;
      this.solverTheories = solverTheories;
      this.solverFeatures = solverFeatures;
    }

    public String getName() {
      return solver.name();
    }

    public String getVersion() {
      return solverVersion;
    }

    public String getTheories() {
      return solverTheories;
    }

    public String getFeatures() {
      return solverFeatures;
    }
  }

  /** This class builds the table row-by-row. */
  public static class RowBuilder {

    private final List<String> lines = new ArrayList<>();
    // Minimum number of lines so that you can be sure a solver was added
    private static final int MIN_NUM_OF_LINES = 4;
    private static final int SOLVER_COLUMN_WIDTH = 11;
    private static final int VERSION_COLUMN_WIDTH = 38;
    private static final int THEORIES_COLUMN_WIDTH = 40;
    private static final int FEATURES_COLUMN_WIDTH = 30;

    private static final String INFO_COLUMN =
        "| %-"
            + SOLVER_COLUMN_WIDTH
            + "s | %-"
            + VERSION_COLUMN_WIDTH
            + "s | %-"
            + THEORIES_COLUMN_WIDTH
            + "s | %-"
            + FEATURES_COLUMN_WIDTH
            + "s |%n";

    private static final String SEPERATOR_LINE =
        "+-"
            + "-".repeat(SOLVER_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(VERSION_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(THEORIES_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(FEATURES_COLUMN_WIDTH)
            + "-+"
            + System.lineSeparator();

    /** The constructor builds the header of the table. */
    public RowBuilder() {
      lines.add(SEPERATOR_LINE);
      lines.add(String.format(INFO_COLUMN, "Solver", "Version", "Theories", "Features"));
      lines.add(SEPERATOR_LINE);
    }

    /**
     * Takes a SolverInfo object and splits it into multiple lines which are added to the row.
     *
     * @param solverInfo the solver with information you want added.
     */
    public void addSolver(SolverInfo solverInfo) {
      List<String> nameLines = Lists.newArrayList(solverInfo.getName());
      List<String> versionLines = formatLines(solverInfo.getVersion(), VERSION_COLUMN_WIDTH);
      List<String> theoriesLines = formatLines(solverInfo.getTheories(), THEORIES_COLUMN_WIDTH);
      List<String> featuresLines = formatLines(solverInfo.getFeatures(), FEATURES_COLUMN_WIDTH);

      int maxLines =
          Math.max(Math.max(versionLines.size(), theoriesLines.size()), featuresLines.size());

      // add empty lines where needed for the layout
      padLines(nameLines, maxLines);
      padLines(versionLines, maxLines);
      padLines(theoriesLines, maxLines);
      padLines(featuresLines, maxLines);

      // build the full lines for this row
      for (int i = 0; i < maxLines; i++) {
        String nameL = nameLines.get(i);
        String versionL = versionLines.get(i);
        String theoriesL = theoriesLines.get(i);
        String featuresL = featuresLines.get(i);

        lines.add(String.format(INFO_COLUMN, nameL, versionL, theoriesL, featuresL));
      }

      lines.add(SEPERATOR_LINE);
    }

    /** Add as many empty lines as needed to fulfill the amount of lines. */
    private void padLines(List<String> linesToPad, int amountOfLines) {
      int numMissingLines = amountOfLines - linesToPad.size();
      for (int i = 0; i < numMissingLines; i++) {
        linesToPad.add("");
      }
    }

    /** split a String into multiple lines where each is shorter than the given maxLength. */
    private List<String> formatLines(String lineToSplit, int maxLength) {
      List<String> versionSplit = Splitter.on(" ").splitToList(lineToSplit);
      List<String> versionLines = new ArrayList<>();
      String line = versionSplit.get(0);
      int lineCounter = line.length();
      for (String current : Iterables.skip(versionSplit, 1)) {
        lineCounter += current.length() + 1;

        if (lineCounter > maxLength) {
          lineCounter = current.length() + 1;
          versionLines.add(line);
          line = current;
        } else {
          line = line + " " + current;
        }
      }
      versionLines.add(line);
      return versionLines;
    }

    @Override
    public String toString() {
      if (lines.size() < MIN_NUM_OF_LINES - 1) {
        return "Could not find any installed SMT-Solvers.";
      }
      return String.join("", lines);
    }
  }
}
