// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
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
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class DebuggingFormulaManager extends FormulaChecks implements FormulaManager {
  private final FormulaManager delegate;

  public DebuggingFormulaManager(FormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    assertThreadLocal();
    return new DebuggingIntegerFormulaManager(delegate.getIntegerFormulaManager(), localFormulas);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    assertThreadLocal();
    return new DebuggingRationalFormulaManager(delegate.getRationalFormulaManager(), localFormulas);
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    assertThreadLocal();
    return new DebuggingBooleanFormulaManager(delegate.getBooleanFormulaManager(), localFormulas);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    assertThreadLocal();
    return new DebuggingArrayFormulaManager(delegate.getArrayFormulaManager(), localFormulas);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    assertThreadLocal();
    return new DebuggingBitvectorFormulaManager(
        delegate.getBitvectorFormulaManager(), localFormulas);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    assertThreadLocal();
    return new DebuggingFloatingPointFormulaManager(
        delegate.getFloatingPointFormulaManager(), localFormulas);
  }

  @Override
  public UFManager getUFManager() {
    assertThreadLocal();
    return new DebuggingUFManager(delegate.getUFManager(), localFormulas);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    assertThreadLocal();
    return new DebuggingSLFormulaManager(delegate.getSLFormulaManager(), localFormulas);
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    assertThreadLocal();
    return new DebuggingQuantifiedFormulaManager(
        delegate.getQuantifiedFormulaManager(), localFormulas);
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    assertThreadLocal();
    return new DebuggingStringFormulaManager(delegate.getStringFormulaManager(), localFormulas);
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    assertThreadLocal();
    return new DebuggingEnumerationFormulaManager(
        delegate.getEnumerationFormulaManager(), localFormulas);
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    assertThreadLocal();
    T var = delegate.makeVariable(formulaType, name);
    addFormulaToContext(var);
    return var;
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    assertThreadLocal();
    for (Formula f : args) {
      assertFormulaInContext(f);
    }
    T app = delegate.makeApplication(declaration, args);
    addFormulaToContext(app);
    return app;
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    assertThreadLocal();
    for (Formula f : args) {
      assertFormulaInContext(f);
    }
    T app = delegate.makeApplication(declaration, args);
    addFormulaToContext(app);
    return app;
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.getFormulaType(formula);
  }

  /* Used by parse() to add all the subterms of the parsed term to the context */
  private class Closure extends DefaultFormulaVisitor<TraversalProcess> {
    @Override
    protected TraversalProcess visitDefault(Formula f) {
      addFormulaToContext(f);
      return TraversalProcess.CONTINUE;
    }
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    assertThreadLocal();
    BooleanFormula formula = delegate.parse(s);
    delegate.visitRecursively(formula, new Closure());
    return formula;
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    assertThreadLocal();
    assertFormulaInContext(pT);
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String dumped = delegate.dumpFormula(pT).toString();
        out.append(dumped);
      }
    };
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula input, Tactic tactic)
      throws InterruptedException {
    assertThreadLocal();
    assertFormulaInContext(input);
    BooleanFormula result = delegate.applyTactic(input, tactic);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    assertThreadLocal();
    assertFormulaInContext(input);
    T result = delegate.simplify(input);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    assertThreadLocal();
    assertFormulaInContext(f);
    return delegate.visit(f, rFormulaVisitor);
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    assertThreadLocal();
    assertFormulaInContext(f);
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    assertThreadLocal();
    assertFormulaInContext(f);
    return delegate.transformRecursively(f, pFormulaVisitor);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    assertThreadLocal();
    assertFormulaInContext(f);
    // All Formulas in the result are subterms of f and don't have to be added to the context again
    return delegate.extractVariables(f);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    assertThreadLocal();
    assertFormulaInContext(f);
    return delegate.extractVariablesAndUFs(f);
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    assertThreadLocal();
    List<Formula> checkAll = new ArrayList<>();
    checkAll.add(f);
    checkAll.addAll(fromToMapping.keySet());
    checkAll.addAll(fromToMapping.values());
    for (Formula term : checkAll) {
      assertFormulaInContext(term);
    }
    T result = delegate.substitute(f, fromToMapping);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    // TODO: We need to check that 'formula' belongs to 'otherManager'
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isValidName(String variableName) {
    assertThreadLocal();
    return delegate.isValidName(variableName);
  }

  @Override
  public String escape(String variableName) {
    assertThreadLocal();
    return delegate.escape(variableName);
  }

  @Override
  public String unescape(String variableName) {
    assertThreadLocal();
    return delegate.unescape(variableName);
  }
}
