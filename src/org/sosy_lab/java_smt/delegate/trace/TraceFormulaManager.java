/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class TraceFormulaManager implements FormulaManager {
  private final FormulaManager delegate;
  private final TraceLogger logger;

  TraceFormulaManager(FormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    return new TraceIntegerFormulaManager(delegate.getIntegerFormulaManager(), logger);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new TraceBooleanFormulaManager(delegate.getBooleanFormulaManager(), logger);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    return new TraceArrayFormulaManager(delegate.getArrayFormulaManager(), logger);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return new TraceBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), logger);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return new TraceFloatingPointFormulaManager(delegate.getFloatingPointFormulaManager(), logger);
  }

  @Override
  public UFManager getUFManager() {
    return new TraceUFManager(delegate.getUFManager(), logger);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    return logger.logDef(
        "mgr",
        String.format("makeVariable(%s, \"%s\")", logger.printFormulaType(formulaType), name),
        () -> delegate.makeVariable(formulaType, name));
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, ImmutableList.copyOf(args));
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    // FIXME Add proper tracing
    return delegate.getFormulaType(formula);
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException, SolverException {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    // FIXME Add proper tracing
    return delegate.extractVariables(f);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    // TODO Write API calls from all contexts into one file to allow us to support this method
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isValidName(String variableName) {
    throw new UnsupportedOperationException();
  }

  @Override
  public String escape(String variableName) {
    throw new UnsupportedOperationException();
  }

  @Override
  public String unescape(String variableName) {
    throw new UnsupportedOperationException();
  }
}
