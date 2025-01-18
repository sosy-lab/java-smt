package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class ParseAndRegenerateTest extends SolverBasedTest0 {
  @Override
  public Solvers solverToUse(){
    return Solvers.Z3;
  }

  public String tellSolver(String smtInput) throws IOException, InterruptedException {
    String command = "z3 -in -smt2";
    Process process = Runtime.getRuntime().exec(command);
    try (BufferedReader reader = new BufferedReader(
        new InputStreamReader(process.getInputStream()));
         BufferedReader errorReader = new BufferedReader(
             new InputStreamReader(process.getErrorStream()));
         var outputStream = process.getOutputStream()) {

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
        throw new RuntimeException("Your Input lead to an error:\n" + errorOutput);
      }
      return output.toString();
    }
  }

  public void runTest(String smtInput)
      throws IOException, InterruptedException, SolverException, InvalidConfigurationException {
    String directZ3Output = tellSolver(smtInput);
    System.out.println("Step 1: DIRECT INPUT TO SOLVER Z3\n"
        + directZ3Output
        + "-----------------------\n");

    BooleanFormula parsed = mgr.universalParseFromString(smtInput);
    Generator.assembleConstraint(parsed);
    String reparsedOutput = String.valueOf(Generator.getLines());
    System.out.println("Step 2: PARSED AND REGENERATED OUTPUT\n"
        + reparsedOutput
        + "-----------------------\n");

    String reparsedAnswer = tellSolver(reparsedOutput);


    System.out.println("Step 3: GIVE REGENERATED OUTPUT TO Z3\n"
        + reparsedAnswer
        + "-----------------------\n");


    assertThat(directZ3Output.startsWith("sat")).isEqualTo(reparsedAnswer.startsWith("sat"));
  }


  @Test
  public void testWithIntegers()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String example =
        "(set-logic QF_LIA)\n"
            + "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-const z Int)\n"
            + "(assert (= x 10))\n"
            + "(assert (= y 10))\n"
            + "(assert (= (+ x y) z))\n";
    runTest(example);
  }
  @Test
  public void testWithStrings()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
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
}

