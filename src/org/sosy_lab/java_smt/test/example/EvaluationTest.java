/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.example;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Locale;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

@SuppressWarnings({"all", "DefaultCharSet"})
public class EvaluationTest extends SolverBasedTest0 {
  @Override
  protected Solvers solverToUse() {
    return Solvers.SOLVERLESS;
  }

  public void runTestOnLocalZ3Terminal(String smtInput)
      throws IOException, InterruptedException, InvalidConfigurationException, SolverException {
    String directZ3Output = tellSolver(smtInput);
    BooleanFormula parsed = mgr.universalParseFromString(smtInput);
    Generator.assembleConstraint(parsed);
    String reparsedOutput = String.valueOf(Generator.getLines());
    String reparsedAnswer = tellSolver(reparsedOutput);
    assertThat(directZ3Output.startsWith("sat")).isEqualTo(reparsedAnswer.startsWith("sat"));
  }

  public void parseAndReparse(BooleanFormula constraint)
      throws InvalidConfigurationException, InterruptedException, SolverException {
    SolverContext solverContext = SolverContextFactory.createSolverContext(Solvers.SOLVERLESS);
    ProverEnvironment proverEnv = solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    IntegerFormulaManager ifm = solverContext.getFormulaManager().getIntegerFormulaManager();
    IntegerFormula a = ifm.makeVariable("a");
    IntegerFormula b = ifm.makeVariable("b");
    IntegerFormula sum = ifm.add(a, b);

    proverEnv.addConstraint(constraint);

    assertThat(proverEnv.isUnsat()).isFalse();
  }

  public void parsedAndReparsedMatchesDirectAPI(String smt2, Solvers solver)
      throws InvalidConfigurationException, InterruptedException, SolverException, IOException {
    Configuration config =
        Configuration.builder()
            .setOption("solver.generateSMTLIB2", "true")
            .setOption("solver.usedSolverBySolverLess", solver.toString().toLowerCase(Locale.ROOT))
            .build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();
    SolverContext actualSolverContext =
        SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(), solver);

    SolverContext solverLessContext =
        SolverContextFactory.createSolverContext(
            config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS);

    ProverEnvironment actualSolverProverEnvironment =
        actualSolverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    ProverEnvironment solverLessProverEnv =
        solverLessContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    System.out.println(actualSolverContext.getSolverName());
    actualSolverProverEnvironment.addConstraint(
        actualSolverContext.getFormulaManager().universalParseFromString(smt2));
    solverLessProverEnv.addConstraint(
        solverLessContext.getFormulaManager().universalParseFromString(smt2));
    boolean directSat = actualSolverProverEnvironment.isUnsat();
    boolean reparsedSat = solverLessProverEnv.isUnsat();
    // SolverLessProverEnvironment is
    // built to
    // parse and reparse the constraint
    assertThat(directSat).isEqualTo(reparsedSat);
  }

  public SolverContext getSolverLessContext() throws InvalidConfigurationException {
    return SolverContextFactory.createSolverContext(Solvers.SOLVERLESS);
  }

  public String tellSolver(String smtInput) throws IOException, InterruptedException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();

    String command = "z3 -in -smt2";
    Process process = Runtime.getRuntime().exec(command);

    try (BufferedReader reader =
            new BufferedReader(new InputStreamReader(process.getInputStream()));
        BufferedReader errorReader =
            new BufferedReader(new InputStreamReader(process.getErrorStream()));
        OutputStream outputStream = process.getOutputStream()) {

      outputStream.write(smtInput.getBytes());
      outputStream.write("(check-sat)\n(get-model)\n(exit)\n".getBytes());
      outputStream.flush();

      StringBuilder output = new StringBuilder();
      String line;
      while ((line = reader.readLine()) != null) {
        output.append(line).append("\n");
      }

      StringBuilder errorOutput = new StringBuilder();
      while ((line = errorReader.readLine()) != null) {
        errorOutput.append(line).append("\n");
      }

      int exitCode = process.waitFor();
      if (exitCode != 0) {
        throw new RuntimeException("Your Input led to an error:\n" + errorOutput);
      }

      return output.toString();
    }
  }

  private boolean isZ3Installed() {
    try {
      Process process = Runtime.getRuntime().exec("z3 -version");
      try (BufferedReader reader =
          new BufferedReader(new InputStreamReader(process.getInputStream()))) {
        return reader.readLine() != null;
      }
    } catch (IOException e) {
      return false;
    }
  }

  @Test
  public void testWithIntegers()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireIntegers();
    String example =
        "(set-logic QF_LIA)\n"
            + "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-const z Int)\n"
            + "(assert (= x 10))\n"
            + "(assert (= y 20))\n"
            + "(assert (= (+ x y) z))\n";
    runTestOnLocalZ3Terminal(example);
    parsedAndReparsedMatchesDirectAPI(example, Solvers.CVC5);
  }

  @Test
  public void testWithStrings()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireStrings();
    String example =
        "(set-logic QF_S)\n"
            + "(declare-const x String)\n"
            + "(declare-const y String)\n"
            + "(declare-const z String)\n"
            + "(assert (= x \"Hello\"))\n"
            + "(assert (= y \" World\"))\n"
            + "(assert (= z (str.++ x y)))\n";
    runTestOnLocalZ3Terminal(example);
    parsedAndReparsedMatchesDirectAPI(example, Solvers.Z3);
  }

  @Test
  public void testMakeFloatingPoint()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireFloats();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";
    runTestOnLocalZ3Terminal(x);
    parsedAndReparsedMatchesDirectAPI(x, Solvers.CVC5);
  }

  @Test
  public void testMakeFloatingPointWithBitvectors()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireBitvectors();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a (fp #b0 #b10000010 #b01000000000000000000000)))\n" // a = 10.0 as FP
            + "(assert (fp.eq b (fp #b0 #b10000010 #b01000000000000000000000)))\n" // b = 10.0 as FP
            + "(assert (fp.eq (fp.add RNE a b) c))\n" // c = a + b
            + "(assert (fp.eq c (fp #b0 #b10000011 #b01000000000000000000000)))\n"; // c = 20.0 as
    // FP
    runTestOnLocalZ3Terminal(x);
    parsedAndReparsedMatchesDirectAPI(x, Solvers.CVC5);
  }

  @Test
  public void testAdditionParseAndReparse()
      throws SolverException, InterruptedException, InvalidConfigurationException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireIntegers();
    SolverContext solverContext = getSolverLessContext();
    IntegerFormulaManager ifm = solverContext.getFormulaManager().getIntegerFormulaManager();
    IntegerFormula a = ifm.makeVariable("a");
    IntegerFormula b = ifm.makeVariable("b");
    IntegerFormula sum = ifm.add(a, b);

    BooleanFormula constraint = ifm.equal(sum, ifm.makeNumber(5));
    parseAndReparse(constraint);
  }

  @Test
  public void testRegexParseAndReparse()
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
    assume().withMessage("Z3 needs to be installed.").that(isZ3Installed()).isTrue();
    requireStrings();
    SolverContext solverContext = getSolverLessContext();
    StringFormulaManager sfm = solverContext.getFormulaManager().getStringFormulaManager();
    StringFormula str = Objects.requireNonNull(sfm).makeVariable("str");
    BooleanFormula result = sfm.in(str, sfm.makeRegex(".*test.*"));
    parseAndReparse(result);
  }
}
