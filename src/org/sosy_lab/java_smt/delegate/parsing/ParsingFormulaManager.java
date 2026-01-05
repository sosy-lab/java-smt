/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ConsoleErrorListener;
import org.antlr.v4.runtime.tree.ParseTree;
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
  private final SymbolManager symbolManager;

  /** Registers all variable/uf declarations made in JavaSMT with the evaluator. * */
  public static class SymbolManager {
    SmtlibEvaluator evaluator;

    SymbolManager(FormulaManager delegate) {
      evaluator = SmtlibEvaluator.link(delegate);
    }

    void addConstant(String name, Formula term) {
      evaluator = evaluator.addConstant(name, term);
    }

    void addFunction(String name, Function<List<Formula>, Formula> function) {
      evaluator = evaluator.addFunction(name, function);
    }

    BooleanFormula evaluate(ParseTree ast) {
      evaluator = evaluator.apply(ast);
      List<BooleanFormula> assertions = evaluator.getAssertions();
      evaluator = evaluator.reset();
      Preconditions.checkArgument(
          assertions.size() == 1,
          "Expecting exactly one assertion, but found %s",
          assertions.size());
      return assertions.get(0);
    }
  }

  public ParsingFormulaManager(FormulaManager pDelegate) {
    delegate = pDelegate;
    symbolManager = new SymbolManager(delegate);
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    return new ParsingIntegerFormulaManager(symbolManager, delegate.getIntegerFormulaManager());
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    return new ParsingRationalFormulaManager(symbolManager, delegate.getRationalFormulaManager());
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    return new ParsingBooleanFormulaManager(symbolManager, delegate.getBooleanFormulaManager());
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    return new ParsingArrayFormulaManager(symbolManager, delegate.getArrayFormulaManager());
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    return new ParsingBitvectorFormulaManager(symbolManager, delegate.getBitvectorFormulaManager());
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    return new ParsingFloatingPointFormulaManager(
        symbolManager, delegate.getFloatingPointFormulaManager());
  }

  @Override
  public UFManager getUFManager() {
    return new ParsingUFManager(symbolManager, delegate, delegate.getUFManager());
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
    return new ParsingStringFormulaManager(symbolManager, delegate.getStringFormulaManager());
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    return delegate.getEnumerationFormulaManager();
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    var term = delegate.makeVariable(formulaType, name);
    symbolManager.addConstant(name, term);
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
  public BooleanFormula equal(Collection<Formula> pArgs) {
    return delegate.equal(pArgs);
  }

  @Override
  public BooleanFormula distinct(Collection<Formula> pArgs) {
    return delegate.distinct(pArgs);
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return delegate.getFormulaType(formula);
  }

  @Override
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
    return symbolManager.evaluate(ast);
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
    return delegate.translateFrom(formula, otherManager);
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
}
