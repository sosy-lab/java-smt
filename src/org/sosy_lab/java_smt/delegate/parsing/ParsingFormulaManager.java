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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ConsoleErrorListener;
import org.antlr.v4.runtime.TokenStream;
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
import org.sosy_lab.java_smt.api.SolverContext;
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
  private final SolverContext solver;

  public record Declarations(
      Map<String, Formula> constants, Map<String, FunctionDeclaration<?>> functions) {

    void addConstant(String name, Formula term) {
      constants.put(name, term);
    }

    void addFunction(String name, FunctionDeclaration<?> declaration) {
      functions.put(name, declaration);
    }
  }

  private final Declarations declarations = new Declarations(new HashMap<>(), new HashMap<>());

  public ParsingFormulaManager(FormulaManager pDelegate, SolverContext pSolver) {
    delegate = pDelegate;
    solver = pSolver;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    return new ParsingIntegerFormulaManager(delegate.getIntegerFormulaManager(), declarations);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    return new ParsingRationalFormulaManager(delegate.getRationalFormulaManager(), declarations);
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new ParsingBooleanFormulaManager(delegate.getBooleanFormulaManager(), declarations);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    return new ParsingArrayFormulaManager(delegate.getArrayFormulaManager(), declarations);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return new ParsingBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), declarations);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return new ParsingFloatingPointFormulaManager(
        delegate.getFloatingPointFormulaManager(), declarations);
  }

  @Override
  public UFManager getUFManager() {
    return new ParsingUFManager(delegate.getUFManager(), this, declarations);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    return delegate.getSLFormulaManager();
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    return delegate.getQuantifiedFormulaManager();
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    return delegate.getStringFormulaManager();
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    return delegate.getEnumerationFormulaManager();
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    var term = delegate.makeVariable(formulaType, name);
    declarations.addConstant(name, term);
    return term;
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    return delegate.makeApplication(declaration, args);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return delegate.makeApplication(declaration, args);
  }

  @Override
  public BooleanFormula makeEqual(Iterable<Formula> pArgs) {
    return delegate.makeEqual(pArgs);
  }

  @Override
  public BooleanFormula makeDistinct(Iterable<Formula> pArgs) {
    return delegate.makeDistinct(pArgs);
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return delegate.getFormulaType(formula);
  }

  private TokenStream lex(String smtlib) {
    var lexer = new SmtlibLexer(CharStreams.fromString(smtlib));
    lexer.removeErrorListener(ConsoleErrorListener.INSTANCE);
    lexer.addErrorListener(new FaultingErrorListener("Lexing error"));
    return new CommonTokenStream(lexer);
  }

  private SmtlibParser.SmtlibContext parse(TokenStream tokens) {
    var parser = new SmtlibParser(tokens);
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE);
    parser.addErrorListener(new FaultingErrorListener("Parsing error"));
    return parser.smtlib();
  }

  @Override
  public List<BooleanFormula> parseAll(String smtlib) throws IllegalArgumentException {
    return SmtlibEvaluator.link(solver, this, SmtlibEvaluator.ParsingMode.FORMULA)
        .apply(parse(lex(smtlib)))
        .getAssertions();
  }

  @Override
  public List<SolverResponse> parseScript(String smtlib)
      throws SolverException, InterruptedException {
    return SmtlibEvaluator.link(solver, this, SmtlibEvaluator.ParsingMode.SCRIPT)
        .apply(parse(lex(smtlib)))
        .getResponses();
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    return delegate.dumpFormula(pT);
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException, SolverException {
    return delegate.applyTactic(input, tactic);
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    return delegate.simplify(input);
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    return delegate.visit(f, rFormulaVisitor);
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return delegate.transformRecursively(f, pFormulaVisitor);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    return delegate.extractVariables(f);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    return delegate.extractVariablesAndUFs(f);
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    return delegate.substitute(f, fromToMapping);
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (otherManager == this) {
      return formula;
    } else {
      return parse(otherManager.dumpFormula(formula).toString());
    }
  }

  @Override
  public boolean isValidName(String variableName) {
    return delegate.isValidName(variableName);
  }

  @Override
  public String escape(String variableName) {
    return delegate.escape(variableName);
  }

  @Override
  public String unescape(String variableName) {
    return delegate.unescape(variableName);
  }

  public Declarations getDefinedSymbols() {
    return new Declarations(
        ImmutableMap.copyOf(declarations.constants), ImmutableMap.copyOf(declarations.functions));
  }
}
