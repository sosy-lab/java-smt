// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import ap.parser.IExpression;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.Visitor;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Lexer;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser;
import org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment;

/**
 * Generates a model by executing Princess with the contents of "Out.smt2" as input and parsing
 * Princess' output model from the file "Model.smt2" back to JavaSMT.
 */
// TODO Add support for arbitrary SMTLIB compatible solvers
public class BinaryModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  AbstractFormulaManager<IExpression, Sort, PrincessEnvironment, ?> mgr;
  private final BooleanFormulaManager bmgr;
  private final IntegerFormulaManager imgr;;
  private final BitvectorFormulaManager bvmgr;
  private final ArrayFormulaManager amgr;
  private final UFManager umgr;

  /** Model.ValuesAssignments for the parsed Princess model. */
  private ImmutableList<ValueAssignment> finalList = ImmutableList.of();

  private boolean isUnsat;

  public BinaryModel(
      AbstractProver<?> prover,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> pCreator,
      AbstractFormulaManager<IExpression, Sort, PrincessEnvironment, ?> pFormulaManager) {
    super(prover, pCreator);
    mgr = pFormulaManager;
    bmgr = mgr.getBooleanFormulaManager();
    imgr = mgr.getIntegerFormulaManager();
    // rmgr = Objects.requireNonNull(formulaManager.getRationalFormulaManager());
    bvmgr = mgr.getBitvectorFormulaManager();
    amgr = mgr.getArrayFormulaManager();
    umgr = mgr.getUFManager();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    throw new UnsupportedOperationException("Princess (Binary) does not support eval().");
  }

  /** Send the query to the Princess binary and store the result. */
  public void runBinary(String input) {
    // FIXME: This method is called twice, once for isUnsat and once to get the model.
    //  Instead of running the solver twice we should cache the result.

    // Write SMTLIB2 script to a file
    try {
      try (Writer fileWriter =
          Files.newBufferedWriter(Path.of("Out.smt2"), Charset.defaultCharset())) {
        fileWriter.write(input);
        fileWriter.flush();
      }
    } catch (IOException e) {
      throw new GeneratorException("Could not write to file");
    }

    // FIXME: Pull the version from the configuration
    String princessJar = "princess_2.13.jar";
    try {
      Process process =
          new ProcessBuilder()
              .command(
                  "java",
                  "-cp",
                  "lib/java/runtime-princess/*:lib/java/runtime-princess/" + princessJar,
                  "ap.CmdlMain",
                  "-logo",
                  "+incremental",
                  "Out.smt2") // FIXME: Use a temporary file (same for Model.smt2)
              .start();

      StringBuilder output = new StringBuilder();
      try (InputStream is = process.getInputStream()) {
        // Wait until the process has finished and throw an exception if an error occurred
        assert process.waitFor() == 0; // TODO: Add an better error message

        try (InputStreamReader isr = new InputStreamReader(is, Charset.defaultCharset())) {
          try (BufferedReader br = new BufferedReader(isr)) {
            // Read the first line to get the result (either "sat" or "unsat")
            isUnsat = br.readLine().equals("unsat");

            // Read the rest of the file to get the model
            String lines = br.readLine();
            while (lines != null) {
              output.append(lines).append("\n");
              lines = br.readLine();
            }

            // Parse the model returned by the binary
            if (!isUnsat) {
              finalList = ImmutableList.copyOf(parseModel(output.toString()));
            }
          }
        }
      }
    } catch (IOException | InterruptedException e) {
      // FIXME: Find a better way to handle IO errors
      throw new RuntimeException(e);
    }
  }

  private List<ValueAssignment> parseModel(String output) {
    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromString(output));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));
    Visitor visitor = new Visitor(mgr, bmgr, imgr, null, bvmgr, amgr, umgr, null, null);
    visitor.visit(parser.start());
    return visitor.getAssignments();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return finalList;
  }

  public BinaryModel getModel() throws ModelException {
    // TODO: Split of the Model with the values as a separate class
    return this;
  }

  @Override
  public String toString() {
    StringBuilder out = new StringBuilder();
    out.append("binary model: \n");
    for (int i = 0; i < finalList.size(); i++) {
      out.append(finalList.get(i));
      out.append("\n");
    }

    return String.valueOf(out);
  }

  public boolean isUnsat() {
    return isUnsat;
  }
}
