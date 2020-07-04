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
import java.util.List;
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

    ListAllSolversWithFeatures listAllSolversWithFeatures = new ListAllSolversWithFeatures();
    String[][] infoArray = listAllSolversWithFeatures.getInformationForAllSolvers();
    listAllSolversWithFeatures.printGridToStdOut(infoArray);
  }

  public ListAllSolversWithFeatures() {}

  /**
   * Prints the infoArray to StdOut in a nice table using the formating method (through printf()).
   * Note that this conforms to the row/columns specified in getInformationForAllSolvers().
   */
  private void printGridToStdOut(String[][] infoArray) {
    if (infoArray == null || infoArray[0].length == 0) {
      System.out.println("Could not find any installed SMT-Solvers.");
      return;
    }

    int maxSolverLength = lineLength(infoArray, 0);
    int maxVersionLength = lineLength(infoArray, 1);
    int maxTheoriesLength = lineLength(infoArray, 2);
    int maxFeaturesLength = lineLength(infoArray, 3);
    String infoColumn =
        "| %-"
            + maxSolverLength
            + "s | %-"
            + maxVersionLength
            + "s | %-"
            + maxTheoriesLength
            + "s | %-"
            + maxFeaturesLength
            + "s |%n";
    String seperatorColumn =
        "+-"
            + "-".repeat(maxSolverLength)
            + "-+-"
            + "-".repeat(maxVersionLength)
            + "-+-"
            + "-".repeat(maxTheoriesLength)
            + "-+-"
            + "-".repeat(maxFeaturesLength)
            + "-+%n";

    System.out.printf(seperatorColumn);
    System.out.printf(infoColumn, "Solver", "Version", "Theories", "Features");
    System.out.printf(seperatorColumn);

    for (String[] s : infoArray) {
      System.out.printf(infoColumn, s[0], s[1], s[2], s[3]);
    }

    System.out.printf(seperatorColumn);
  }

  /**
   * Gathers information about every available solver into a 2-Dimensional array representing rows
   * and columns of the later table. Columns represent (in order): Solver, Version, Theories,
   * Features. Rows represent the solvers available to the installed JavaSMT.
   */
  private String[][] getInformationForAllSolvers() throws SolverException, InterruptedException {
    List<String[]> info = new ArrayList<>();
    for (Solvers s : Solvers.values()) {
      String[] solverInfo = getSolverInformation(s);
      if (solverInfo != null && solverInfo.length == 4) {
        info.add(solverInfo);
      }
    }
    return info.toArray(new String[0][0]);
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
  private String[] getSolverInformation(Solvers solver)
      throws SolverException, InterruptedException {
    List<String> info = new ArrayList<>();

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = LogManager.createNullLogManager();
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

      info.add(solver.name());

      info.add(context.getVersion());

      info.add(getTheories(context));

      info.add(getFeatures(context));
    } catch (InvalidConfigurationException e) {
      // Catches missing solvers
    }

    return info.toArray(new String[0]);
  }

  /**
   * Checks the solver entered for features. Features checked: Optimization, UnsatCore,
   * UnsatCoreWithAssumptions, Assumptions, AllSat, Interpolation
   *
   * @param context SolverContext you want to check for features.
   * @return String with the features of the entered solver separated by a comma. Empty if none
   *     available.
   */
  private String getFeatures(SolverContext context) throws SolverException, InterruptedException {
    List<String> features = new ArrayList<>();

    // Optimization: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      if (prover != null) {
        features.add("Optimization");
      }
    } catch (UnsupportedOperationException e) {
    }

    // Interpolation: Will throw UnsupportedOperationException in creation of prover if not
    // available.
    try (InterpolatingProverEnvironment<?> prover =
        context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS)) {
      if (prover != null) {
        features.add("Interpolation");
      }
    } catch (UnsupportedOperationException e) {
    }

    // UnsatCore: throws UnsupportedOperationException if not available.
    // TODO: check behavior with null argument properly
    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      if (prover.getUnsatCore() != null) {
        features.add("UnsatCore");
      }
    } catch (UnsupportedOperationException e) {
    } catch (Exception e) {
      features.add("UnsatCore");
    }

    // UnsatCoreOverAssumptions: throws NullPointerException if available.
    try (ProverEnvironment prover =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      prover.unsatCoreOverAssumptions(null);
    } catch (UnsupportedOperationException e) {
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
      }
    }

    // We don't care about the return value, just that it doesn't throw an
    // UnsupportedOperationException.
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      try {
        prover.isUnsatWithAssumptions(ImmutableList.of());
        features.add("Assumptions");
      } catch (UnsupportedOperationException e) {
      }
    }

    return String.join(",", features);
  }

  /**
   * This method checks the SolverContext entered for all its available theories and gives them back
   * as String with each theory separated by a comma.
   *
   * @param context JavaSMT SolverContext of the Solver you want to check for theories.
   * @return String of all supported theories except Booleans, separated by a comma. Empty if none
   *     available.
   */
  private String getTheories(SolverContext context) {
    List<String> theories = new ArrayList<>();
    FormulaManager mgr = context.getFormulaManager();

    // Every solver has to have Bool-Theory, should we add it?
    try {
      if (mgr.getIntegerFormulaManager() != null) {
        theories.add("Integer");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getBitvectorFormulaManager() != null) {
        theories.add("Bitvector");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getRationalFormulaManager() != null) {
        theories.add("Rational");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getFloatingPointFormulaManager() != null) {
        theories.add("Float");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getArrayFormulaManager() != null) {
        theories.add("Array");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getQuantifiedFormulaManager() != null) {
        theories.add("Quantifier");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getUFManager() != null) {
        theories.add("UF");
      }
    } catch (UnsupportedOperationException e) {
    }

    try {
      if (mgr.getSLFormulaManager() != null) {
        theories.add("Seperation-Logic");
      }
    } catch (UnsupportedOperationException e) {
    }

    return String.join(",", theories);
  }

  /**
   * Checks the infoArray for the length of the given column.
   *
   * @param columnToCheck column of the infoArray you want the length for.
   * @return length of String in column, but at least 8 (max length of the descriptor Strings).
   */
  private int lineLength(String[][] infoArray, int columnToCheck) {
    if (columnToCheck > 3 || columnToCheck < 0) {
      return 8;
    }
    int length = 8;
    for (String[] s : infoArray) {
      int checkedLength = s[columnToCheck].length();
      if (length < checkedLength) {
        length = checkedLength;
      }
    }
    return length;
  }
}
