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
package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class StatisticsFormulaManager implements FormulaManager {

  private final FormulaManager delegate;
  private final SolverStatistics stats;

  protected StatisticsFormulaManager(FormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    return new StatisticsIntegerFormulaManager(delegate.getIntegerFormulaManager(), stats);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    return new StatisticsRationalFormulaManager(delegate.getRationalFormulaManager(), stats);
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new StatisticsBooleanFormulaManager(delegate.getBooleanFormulaManager(), stats);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    return new StatisticsArrayFormulaManager(delegate.getArrayFormulaManager(), stats);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return new StatisticsBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), stats);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return new StatisticsFloatingPointFormulaManager(
        delegate.getFloatingPointFormulaManager(), stats);
  }

  @Override
  public UFManager getUFManager() {
    return new StatisticsUFManager(delegate.getUFManager(), stats);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    return new StatisticsSLFormulaManager(delegate.getSLFormulaManager(), stats);
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    return new StatisticsQuantifiedFormulaManager(delegate.getQuantifiedFormulaManager(), stats);
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> pFormulaType, String pName) {
    return delegate.makeVariable(pFormulaType, pName);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> pDeclaration, List<? extends Formula> pArgs) {
    return delegate.makeApplication(pDeclaration, pArgs);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> pDeclaration, Formula... pArgs) {
    return delegate.makeApplication(pDeclaration, pArgs);
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    return delegate.getFormulaType(pFormula);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    return delegate.parse(pS);
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String dump;
        dump = delegate.dumpFormula(pT).toString(); // the work is done here
        out.append(dump);
      }
    };
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula pInput, Tactic pTactic)
      throws InterruptedException {
    return delegate.applyTactic(pInput, pTactic);
  }

  @Override
  public <T extends Formula> T simplify(T pInput) throws InterruptedException {
    return delegate.simplify(pInput);
  }

  @Override
  public <R> R visit(Formula pF, FormulaVisitor<R> pFormulaVisitor) {
    return delegate.visit(pF, pFormulaVisitor);
  }

  @Override
  public void visitRecursively(Formula pF, FormulaVisitor<TraversalProcess> pFormulaVisitor) {
    delegate.visitRecursively(pF, pFormulaVisitor);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T pF, FormulaTransformationVisitor pFormulaVisitor) {
    return delegate.transformRecursively(pF, pFormulaVisitor);
  }

  @Override
  public Map<String, Formula> extractVariables(Formula pF) {
    return delegate.extractVariables(pF);
  }

  @Override
  public Map<String, Formula> extractVariablesAndUFs(Formula pF) {
    return delegate.extractVariablesAndUFs(pF);
  }

  @Override
  public <T extends Formula> T substitute(
      T pF, Map<? extends Formula, ? extends Formula> pFromToMapping) {
    return delegate.substitute(pF, pFromToMapping);
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula pFormula, FormulaManager pOtherContext) {
    return delegate.translateFrom(pFormula, pOtherContext);
  }

  @Override
  public boolean isValidName(String pVariableName) {
    return delegate.isValidName(pVariableName);
  }

  @Override
  public String escape(String pVariableName) {
    return delegate.escape(pVariableName);
  }

  @Override
  public String unescape(String pVariableName) {
    return delegate.unescape(pVariableName);
  }
}
