/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.example;

import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Supplier;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment.AllSatCallback;
import org.sosy_lab.java_smt.api.BooleanFormula;
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
// TODO: find shorter name
public class ListAllSolversWithFeatures {

  public static void main(String[] args) throws SolverException, InterruptedException {

    ListAllSolversWithFeatures laswf = new ListAllSolversWithFeatures();
    RowBuilder rowBuilder = laswf.new RowBuilder();
    laswf.getInformationForAllSolvers(rowBuilder);
    System.out.println(rowBuilder.toString());
  }

  public ListAllSolversWithFeatures() {}

  /**
   * Gathers information about every available solver into a 2-Dimensional array representing rows
   * and columns of the later table. Columns represent (in order): Solver, Version, Theories,
   * Features. Rows represent the solvers available to the installed JavaSMT.
   */
  private void getInformationForAllSolvers(
      RowBuilder rowBuilder)
      throws SolverException, InterruptedException {
    for (Solvers s : Solvers.values()) {
      SolverInfo solverInfo = getSolverInformation(s);
      if (solverInfo != null) {
        rowBuilder.addSolver(solverInfo);
      }
    }
  }

  /**
   * Checks for solver-name, version, theories and features and packs them into a String[] of length
   * 4.
   *
   * @param solver to check for information. Taken from Solvers enum only.
   * @return String[] of length 4 of the solver you entered. Array content as String in the
   *     following order: SolverName, SolverVersion, SolverTheories, SolverFeatures. String[] length
   *     0 if invalid solver.
   */
  private SolverInfo getSolverInformation(
      Solvers solver)
      throws SolverException, InterruptedException {

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = LogManager.createNullLogManager();
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

      Solvers name = solver;

      String version = context.getVersion();

      String theories = String.join(", ", getTheories(context));

      String features = String.join(", ", getFeatures(context));

      return new SolverInfo(name, version, theories, features);
    } catch (InvalidConfigurationException e) {
      // Catches missing solvers
      return null;
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
  private List<String> getFeatures(SolverContext context)
      throws SolverException, InterruptedException {
    List<String> features = new ArrayList<>();

    // Optimization: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      if (prover != null) {
        features.add("Optimization");
      }
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    }

    // Interpolation: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (InterpolatingProverEnvironment<?> prover =
        context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS)) {
      if (prover != null) {
        features.add("Interpolation");
      }
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    }

    // UnsatCore: throws UnsupportedOperationException if not available.
    // TODO: check behavior with null argument properly
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      if (prover.getUnsatCore() != null) {
        features.add("UnsatCore");
      }
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    } catch (Exception e) {
      features.add("UnsatCore");
    }

    // UnsatCoreOverAssumptions: throws NullPointerException if available.
    try (ProverEnvironment prover =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      prover.unsatCoreOverAssumptions(null);
    } catch (UnsupportedOperationException e) {
      // ignore, feature is not supported.
    } catch (NullPointerException e) {
      features.add("UnsatCore /w Assumption");
    }

    // TODO: Remove or rework to check if solver overrides!
    // AllSat: All solvers support this through JavaSMT.
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_ALL_SAT)) {
      try {
        if (prover.allSat(
                new AllSatCallback<>() {

                  List<List<BooleanFormula>> models = new ArrayList<>();

                  @Override
                  public void apply(List<BooleanFormula> pModel) {
                    models.add(pModel);
                  }

                  @Override
                  public List<List<BooleanFormula>> getResult() {
                    return models;
                  }
                },
                ImmutableList.of())
            != null) {
          features.add("AllSAT");
        }
      } catch (UnsupportedOperationException e) {
        // ignore, feature is not supported.
      }
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
    addIfAvailable(theories, mgr::getSLFormulaManager, "Seperation-Logic");

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

  private class SolverInfo {
    private Solvers solver;
    private String solverVersion;
    private String solverTheories;
    private String solverFeatures;

    /**
     * Saves the information of an solver.
     *
     * @param solver Solvers enum object for a solver.
     * @param solverVersion Solver version.
     * @param solverTheories Solver theories.
     * @param solverFeatures Solver features.
     */
    public SolverInfo(
        Solvers solver,
        String solverVersion,
        String solverTheories,
        String solverFeatures) {
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

  private class RowBuilder {
    private List<String> lines = new ArrayList<>();
    // Minimum number of lines so that you can be sure a solver was added
    private final int MIN_NUM_OF_LINES = 4;
    private final int SOLVER_COLUMN_WIDTH = 15;
    private final int VERSION_COLUMN_WIDTH = 40;
    private final int THEORIES_COLUMN_WIDTH = 25;
    private final int FEATURES_COLUMN_WIDTH = 25;

    private String infoColumn =
        "| %-"
            + SOLVER_COLUMN_WIDTH
            + "s | %-"
            + VERSION_COLUMN_WIDTH
            + "s | %-"
            + THEORIES_COLUMN_WIDTH
            + "s | %-"
            + FEATURES_COLUMN_WIDTH
            + "s |%n";

    private String seperatorLine =
        "+-"
            + "-".repeat(SOLVER_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(VERSION_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(THEORIES_COLUMN_WIDTH)
            + "-+-"
            + "-".repeat(FEATURES_COLUMN_WIDTH)
            + "-+%n";

    /**
     *
     */
    public RowBuilder() {
      lines.add(String.format(seperatorLine));
      lines.add(String.format(infoColumn, "Solver", "Version", "Theories", "Features"));
      lines.add(String.format(seperatorLine));
    }

    /**
     * Takes a SolverInfo object and splits it into lines which are added to the final String.
     *
     * @param solverInfo the solver with information you want added.
     */
    public void addSolver(SolverInfo solverInfo) {
      List<String> nameLines = new LinkedList<>();
      List<String> versionLines = getLines(solverInfo.getVersion(), VERSION_COLUMN_WIDTH);
      List<String> TheoriesLines = getLines(solverInfo.getTheories(), THEORIES_COLUMN_WIDTH);
      List<String> FeaturesLines = getLines(solverInfo.getFeatures(), FEATURES_COLUMN_WIDTH);

      nameLines.add(solverInfo.getName());

      int maxLines =
          Math.max(Math.max(versionLines.size(), TheoriesLines.size()), FeaturesLines.size());

      padLines(nameLines, maxLines);
      padLines(versionLines, maxLines);
      padLines(TheoriesLines, maxLines);
      padLines(FeaturesLines, maxLines);

      for (int i = 0; i < maxLines; i++) {
        String nameL = nameLines.get(i);
        String versionL = versionLines.get(i);
        String theoriesL = TheoriesLines.get(i);
        String featuresL = FeaturesLines.get(i);

        lines.add(String.format(infoColumn, nameL, versionL, theoriesL, featuresL));
      }

      lines.add(String.format(seperatorLine));
    }

    private void padLines(List<String> linesToPad, int amountOfLines) {
      if (linesToPad.size() == amountOfLines) {
        return;
      }
      int loop = amountOfLines - linesToPad.size();
      for (int i = 0; i < loop; i++) {
        if (Math.floorMod(i, 2) == 1) {
          linesToPad.add(0, "");
        } else {
          linesToPad.add(linesToPad.size(), "");
        }
      }
    }

    private List<String> getLines(String lineToSplit, int maxLength) {
      List<String> versionSplit =
          new LinkedList<>(Arrays.asList(lineToSplit.split(" ")));
      List<String> versionLines = new LinkedList<>();
      String line = versionSplit.get(0);
      int lineCounter = line.length();
      for (int i = 1; i < versionSplit.size(); i++) {
        String current = versionSplit.get(i);
        lineCounter += current.length() + 1;

        if ((lineCounter - 1) > maxLength - 1) {
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
