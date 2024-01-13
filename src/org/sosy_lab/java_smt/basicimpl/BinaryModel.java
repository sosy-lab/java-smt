/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.basicimpl;

import ap.parser.IExpression;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
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
public class BinaryModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  AbstractFormulaManager<IExpression, Sort, PrincessEnvironment, ?> mgr;
  private final BooleanFormulaManager bmgr;
  private final IntegerFormulaManager imgr;
  // private final RationalFormulaManager rmgr;
  private final BitvectorFormulaManager bvmgr;
  private final ArrayFormulaManager amgr;
  private final UFManager umgr;

  private List<ValueAssignment> assignments;

  /** Model.ValuesAssignments for the parsed Princess model */
  public ImmutableList<ValueAssignment> finalList;

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
    assignments = new ArrayList<>();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    throw new UnsupportedOperationException("Princess (Binary) does not support eval().");
  }

  /** generates an SMT-LIB2 model from Princess and writes it into a file "Model.smt2" */
  public void getOutput() {
    // FIXME: This method is called twice, once for isUnsat and once to get the model.
    //  Instead of running the solver twice we should cache the result.

    // FIXME: This method uses the standalone binary, which has to be copied to the main folder.
    //  We should switch to the version that is already included in our distribution.

    try {
      Process process =
          new ProcessBuilder()
              .command(
                  "java",
                  "-cp",
                  "princess_all-2023-06-19.jar",
                  "ap.CmdlMain",
                  "-logo",
                  "+incremental",
                  "Out.smt2")
              .start();

      StringBuilder output = new StringBuilder();
      try (InputStream is = process.getInputStream()) {
        // Wait until the process has finished and throw an exception if an error occurred
        assert process.waitFor() == 0;

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

            // Store it in Model.smt2
            Generator.writeToFile(String.valueOf(output), "Model.smt2");
          }
        }
      }
    } catch (IOException | InterruptedException e) {
      // FIXME: Find a better way to handle IO errors
      throw new RuntimeException(e);
    }
  }

  private List<ValueAssignment> parseModel(String pString) {
    try {
      smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromFileName(pString));
      smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));
      Visitor visitor = new Visitor(mgr, bmgr, imgr, null, bvmgr, amgr, umgr);
      visitor.visit(parser.start());
      assignments = visitor.getAssignments();
      return assignments;
    } catch (IOException e) {
      // FIXME: Find a better way to handle IO errors
      throw new RuntimeException(e);
    }
  }

  protected void getAssignments() throws ModelException {
    getOutput();
    if (!isUnsat) {
      assignments = parseModel("Model.smt2");
    } else {
      throw new ModelException("Formula has to be sat in order to retrieve a model.");
    }
    finalList = ImmutableList.copyOf(assignments);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return finalList;
  }

  public BinaryModel getModel() throws ModelException {
    getAssignments();
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
