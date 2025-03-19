package org.sosy_lab.java_smt.test.example;

import static com.google.common.truth.Truth.assertThat;

import java.io.IOException;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class ParseGenerateAndReparseTest {

  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, SolverException, IOException {

    if (args.length < 2) {
      System.err.println("Usage: java ParseGenerateAndReparseTest <smt2-string> <solver>");
      System.exit(1);
    }

    String smt2 = args[0];
    String solverName = args[1];

    // Try to get the solver
    Solvers solver;
    try {
      solver = Solvers.valueOf(solverName.toLowerCase());
    } catch (IllegalArgumentException e) {
      System.err.println("Invalid solver name: " + solverName);
      System.exit(1);
      return; // Unreachable, aber notwendig für Compiler
    }

    // JavaSMT-Konfiguration
    Configuration config =
        Configuration.builder()
            .setOption("solver.generateSMTLIB2", "true")
            .setOption("solver.usedSolverBySolverLess", solverName)
            .build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    // Solver-Kontext für Z3
    SolverContext z3solverContext =
        SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(), solver);

    // Solverless Kontext (nutzt Z3, aber parsed Constraint vorher neu)
    SolverContext solverLessContext =
        SolverContextFactory.createSolverContext(
            config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS);

    // Prover Environments für beide Kontexte
    ProverEnvironment z3proverEnv =
        z3solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    ProverEnvironment solverLessProverEnv =
        solverLessContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);

    // Constraint hinzufügen
    z3proverEnv.addConstraint(z3solverContext.getFormulaManager().universalParseFromString(smt2));
    solverLessProverEnv.addConstraint(
        solverLessContext.getFormulaManager().universalParseFromString(smt2));

    // Ergebnisse vergleichen
    boolean z3Sat = z3proverEnv.isUnsat();
    boolean reparsedSat = solverLessProverEnv.isUnsat();

    assertThat(z3Sat).isEqualTo(reparsedSat);

    System.out.println("Test erfolgreich: " + z3Sat);
  }
}
