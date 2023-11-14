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

package org.sosy_lab.java_smt.utils.Generators;

import com.google.common.collect.ImmutableList;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import javax.annotation.Nullable;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.utils.Parsers.Visitor;
import org.sosy_lab.java_smt.utils.Parsers.smtlibv2Lexer;
import org.sosy_lab.java_smt.utils.Parsers.smtlibv2Parser;

public class UniversalModel extends AbstractModel {

  private final String path = "/home/janel/Desktop/Studium/Semester_6/Bachelorarbeit"
      + "/nochmalneu/";

  AbstractFormulaManager<Formula, Formula, Formula, ?> formulaManager;
  private final BooleanFormulaManager bmgr;
  private final IntegerFormulaManager imgr;
  //private final RationalFormulaManager rmgr;
  private final BitvectorFormulaManager bvmgr;
  private final ArrayFormulaManager amgr;
  private final UFManager umgr;

  private List<ValueAssignment> assignments;
  private ImmutableList<ValueAssignment> finalList;
  private boolean isUnsat;



  public UniversalModel(
      AbstractProver<?> prover,
      AbstractFormulaManager<Formula, Formula, Formula, ?> pFormulaManager) {
    super( prover, pFormulaManager);
    formulaManager = pFormulaManager;
    bmgr = formulaManager.getBooleanFormulaManager();
    imgr = formulaManager.getIntegerFormulaManager();
    //rmgr = Objects.requireNonNull(formulaManager.getRationalFormulaManager());
    bvmgr = formulaManager.getBitvectorFormulaManager();
    amgr = formulaManager.getArrayFormulaManager();
    umgr = formulaManager.getUFManager();
    assignments = new ArrayList<>();

  }

  public ImmutableList<ValueAssignment> listToImmutable(List<ValueAssignment> pList) {
    ImmutableList<ValueAssignment> immutableList = ImmutableList.copyOf(pList);
    return immutableList;
  }

  public String getOutput() throws IOException {
    StringBuilder output = new StringBuilder();

    Process process = new ProcessBuilder("/home/janel/Desktop/Studium/Semester_6/Bachelorarbeit"
        + "/Princess/princess-bin-2023-06-19/princess",
        "+incremental", (path + "Out.smt2")).start();
    InputStream is = process.getInputStream();
    InputStreamReader isr = new InputStreamReader(is);
    BufferedReader br = new BufferedReader(isr);
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
    Generator.writeToFile(String.valueOf(output), (path + "Model.smt2"));
    return String.valueOf(output);
  }

  public List<ValueAssignment> parseModel(String pString)
      throws IOException {
    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromFileName(pString));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));
    Visitor visitor = new Visitor(formulaManager, bmgr, imgr, null, bvmgr, amgr, umgr);
    visitor.visit(parser.start());
    assignments = visitor.getAssignments();
    return assignments;
  }

  public List<ValueAssignment> parseModelFromString(String pString)
      throws IOException {
    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromString(pString));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));
    Visitor visitor = new Visitor(formulaManager, bmgr, imgr, null, bvmgr, amgr, umgr);
    visitor.visit(parser.start());
    assignments = visitor.getAssignments();
    return assignments;
  }

  public List<ValueAssignment> getAssignments()
      throws IOException, ModelException {
    getOutput();
    if (! isUnsat) {
      assignments = parseModel(path + "Model.smt2");
    } else {
      throw new ModelException("Formula has to be sat in order to retrieve a model.");
    }
    finalList = listToImmutable(assignments);


    return assignments;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {

    return finalList;
  }

  public UniversalModel getModel()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException,
             ModelException {
    getOutput();
    getAssignments();
    return this;
  }

  @Nullable
  @Override
  protected Formula evalImpl(Object formula) {
    return null;
  }

  @Override
  public String toString() {
    StringBuilder out = new StringBuilder();
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

