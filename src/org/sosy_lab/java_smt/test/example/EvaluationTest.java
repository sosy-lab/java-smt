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
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

@SuppressWarnings({"all", "DefaultCharSet"})
public class EvaluationTest extends SolverBasedTest0 {
  @Override
  protected Solvers solverToUse() {
    return Solvers.SOLVERLESS;
  }

  @Before
  public void setUp() {
    assume().withMessage("This test is only for local usage.").that(true).isFalse();
  }

  public void runTest(String smtInput)
      throws IOException, InterruptedException, InvalidConfigurationException, SolverException {
    String directZ3Output = tellSolver(smtInput);
    System.out.println(
        "Step 1: DIRECT OUTPUT FROM SOLVER Z3\n" + directZ3Output + "-----------------------\n");
    BooleanFormula parsed = mgr.universalParseFromString(smtInput);
    Generator.assembleConstraint(parsed);
    String reparsedOutput = String.valueOf(Generator.getLines());
    System.out.println(
        "Step 2: PARSED AND REGENERATED OUTPUT\n" + reparsedOutput + "-----------------------\n");
    String reparsedAnswer = tellSolver(reparsedOutput);
    System.out.println(
        "Step 3: GIVE REGENERATED OUTPUT TO Z3\n" + reparsedAnswer + "-----------------------\n");
    assertThat(directZ3Output.startsWith("sat")).isEqualTo(reparsedAnswer.startsWith("sat"));
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

  public void runTestWithAPIConstraint(BooleanFormula constraint)
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    if (!Generator.isLoggingEnabled()) {
      throw new InvalidConfigurationException(
          "Logging must be enabled to run this test!"
              + "Also make sure that it was enabled while creating the constraint!");
    }
    Generator.assembleConstraint(constraint);
    String x = String.valueOf(Generator.getLines());
    runTest(x);
    Generator.resetGenerator();
  }

  @Test
  public void testWithIntegers()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    String example =
        "(set-logic QF_LIA)\n"
            + "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-const z Int)\n"
            + "(assert (= x 10))\n"
            + "(assert (= y 20))\n"
            + "(assert (= (+ x y) z))\n";
    runTest(example);
  }

  @Test
  public void testWithStrings()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String example =
        "(set-logic QF_S)\n"
            + "(declare-const x String)\n"
            + "(declare-const y String)\n"
            + "(declare-const z String)\n"
            + "(assert (= x \"Hello\"))\n"
            + "(assert (= y \" World\"))\n"
            + "(assert (= z (str.++ x y)))\n";
    runTest(example);
  }

  @Test
  public void testMakeFloatingPoint()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    requireFloats();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";
    runTest(x);
  }

  @Test
  public void testMakeFloatingPointWithBitvectors()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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
    runTest(x);
  }

  private ProverEnvironment proverEnv;
  private SolverContext solverContext;
  private IntegerFormulaManager ifm;

  @Test
  public void testAddition()
      throws SolverException, InterruptedException, InvalidConfigurationException {
    solverContext = SolverContextFactory.createSolverContext(Solvers.SOLVERLESS);
    proverEnv = solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    ifm = solverContext.getFormulaManager().getIntegerFormulaManager();
    IntegerFormula a = ifm.makeVariable("a");
    IntegerFormula b = ifm.makeVariable("b");
    IntegerFormula sum = ifm.add(a, b);

    BooleanFormula constraint = ifm.equal(sum, ifm.makeNumber(5));
    proverEnv.addConstraint(constraint);

    assertThat(proverEnv.isUnsat()).isFalse();
  }
}
