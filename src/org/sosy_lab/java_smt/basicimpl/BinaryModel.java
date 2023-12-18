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
import java.io.File;
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
import org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment;
import org.sosy_lab.java_smt.utils.parserUtils.smtlibv2Lexer;
import org.sosy_lab.java_smt.utils.parserUtils.smtlibv2Parser;

/**
 * Generates a model by executing Princess with the contents of "Out.smt2" as input and parsing
 * Princess' output model from the file "Model.smt2" back to JavaSMT.
 */
public class BinaryModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final String filePath = System.getProperty("user.dir");

  AbstractFormulaManager<IExpression, Sort, PrincessEnvironment, ?> fmgr;
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
      AbstractFormulaManager<IExpression, Sort, PrincessEnvironment, ?> pFormulaManager) {
    super(prover, pFormulaManager);
    fmgr = pFormulaManager;
    bmgr = formulaManager.getBooleanFormulaManager();
    imgr = formulaManager.getIntegerFormulaManager();
    // rmgr = Objects.requireNonNull(formulaManager.getRationalFormulaManager());
    bvmgr = formulaManager.getBitvectorFormulaManager();
    amgr = formulaManager.getArrayFormulaManager();
    umgr = formulaManager.getUFManager();
    assignments = new ArrayList<>();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    return null;
  }

  protected ImmutableList<ValueAssignment> listToImmutable(List<ValueAssignment> pList) {
    ImmutableList<ValueAssignment> immutableList = ImmutableList.copyOf(pList);
    return immutableList;
  }

  /**
   * generates an SMT-LIB2 model from Princess and writes it into a file "Model.smt2"
   *
   * @throws IOException if writing to file fails
   */
  public void getOutput() throws IOException {

    String fileName = "/princess_all-2023-06-19.jar";
    String princessJar = filePath + fileName;
    new File(princessJar).setExecutable(true);

    Process process =
        Runtime.getRuntime()
            .exec("java -jar " + princessJar + " +incremental " + filePath + "/Out.smt2");

    StringBuilder output = new StringBuilder();
    try (InputStream is = process.getInputStream()) {
      try {
        process.waitFor();
      } catch (InterruptedException pE) {
        throw new RuntimeException(pE);
      }
      try (InputStreamReader isr = new InputStreamReader(is, Charset.defaultCharset())) {
        try (BufferedReader br = new BufferedReader(isr)) {
          String lines;
          while ((lines = br.readLine()) != null) {
            output.append(lines).append("\n");
          }
          if (String.valueOf(output).startsWith("un")) {
            isUnsat = true;
            output.delete(0, 5);
          } else {
            isUnsat = false;
            output.delete(0, 3);
          }
          Generator.writeToFile(String.valueOf(output), (filePath + "/Model.smt2"));
        }
      }
    }
  }

  private List<ValueAssignment> parseModel(String pString) throws IOException {
    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromFileName(pString));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));
    Visitor visitor = new Visitor(formulaManager, bmgr, imgr, null, bvmgr, amgr, umgr);
    visitor.visit(parser.start());
    assignments = visitor.getAssignments();
    return assignments;
  }

  protected void getAssignments() throws IOException, ModelException {
    getOutput();
    if (!isUnsat) {
      assignments = parseModel(filePath + "/Model.smt2");
    } else {
      throw new ModelException("Formula has to be sat in order to retrieve a model.");
    }
    finalList = listToImmutable(assignments);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {

    return finalList;
  }

  public BinaryModel getModel() throws IOException, ModelException {
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

  public void setUnsat(boolean pUnsat) {
    isUnsat = pUnsat;
  }
}