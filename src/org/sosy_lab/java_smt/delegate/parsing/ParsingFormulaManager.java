/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ConsoleErrorListener;
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
import org.sosy_lab.java_smt.basicimpl.parser.FaultingErrorListener;
import org.sosy_lab.java_smt.basicimpl.parser.SmtlibEvaluator;
import org.sosy_lab.java_smt.basicimpl.parser.SmtlibLexer;
import org.sosy_lab.java_smt.basicimpl.parser.SmtlibParser;

public class ParsingFormulaManager implements FormulaManager {
  private final FormulaManager delegate;

  public ParsingFormulaManager(FormulaManager pDelegate) {
    delegate = pDelegate;
  }

  public IntegerFormulaManager getIntegerFormulaManager() {
    return delegate.getIntegerFormulaManager();
  }

  public RationalFormulaManager getRationalFormulaManager() {
    return delegate.getRationalFormulaManager();
  }

  public BooleanFormulaManager getBooleanFormulaManager() {
    return delegate.getBooleanFormulaManager();
  }

  public ArrayFormulaManager getArrayFormulaManager() {
    return delegate.getArrayFormulaManager();
  }

  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return delegate.getBitvectorFormulaManager();
  }

  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return delegate.getFloatingPointFormulaManager();
  }

  public UFManager getUFManager() {
    return delegate.getUFManager();
  }

  public SLFormulaManager getSLFormulaManager() {
    return delegate.getSLFormulaManager();
  }

  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    return delegate.getQuantifiedFormulaManager();
  }

  public StringFormulaManager getStringFormulaManager() {
    return delegate.getStringFormulaManager();
  }

  public EnumerationFormulaManager getEnumerationFormulaManager() {
    return delegate.getEnumerationFormulaManager();
  }

  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    return delegate.makeVariable(formulaType, name);
  }

  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    return delegate.makeApplication(declaration, args);
  }

  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return delegate.makeApplication(declaration, args);
  }

  public BooleanFormula equal(Collection<Formula> pArgs) {
    return delegate.equal(pArgs);
  }

  public BooleanFormula distinct(Collection<Formula> pArgs) {
    return delegate.distinct(pArgs);
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return delegate.getFormulaType(formula);
  }

  public BooleanFormula parse(String s) throws IllegalArgumentException {
    var input = CharStreams.fromString(s);
    var lexer = new SmtlibLexer(input);
    lexer.removeErrorListener(ConsoleErrorListener.INSTANCE);
    lexer.addErrorListener(new FaultingErrorListener("Lexing error"));
    var tokens = new CommonTokenStream(lexer);
    var parser = new SmtlibParser(tokens);
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE);
    parser.addErrorListener(new FaultingErrorListener("Parsing error"));
    var ast = parser.smtlib();
    return SmtlibEvaluator.link(this).apply(ast).getAssertions().get(0);
  }

  public Appender dumpFormula(BooleanFormula pT) {
    return delegate.dumpFormula(pT);
  }

  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException, SolverException {
    return delegate.applyTactic(input, tactic);
  }

  public <T extends Formula> T simplify(T input) throws InterruptedException {
    return delegate.simplify(input);
  }

  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    return delegate.visit(f, rFormulaVisitor);
  }

  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return delegate.transformRecursively(f, pFormulaVisitor);
  }

  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    return delegate.extractVariables(f);
  }

  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    return delegate.extractVariablesAndUFs(f);
  }

  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    return delegate.substitute(f, fromToMapping);
  }

  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    return delegate.translateFrom(formula, otherManager);
  }

  public boolean isValidName(String variableName) {
    return delegate.isValidName(variableName);
  }

  public String escape(String variableName) {
    return delegate.escape(variableName);
  }

  public String unescape(String variableName) {
    return delegate.unescape(variableName);
  }
}
