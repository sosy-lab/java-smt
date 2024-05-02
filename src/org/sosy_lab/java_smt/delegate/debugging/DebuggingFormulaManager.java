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
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class DebuggingFormulaManager implements FormulaManager {
  private final FormulaManager delegate;
  private final DebuggingContext debugging;

  public DebuggingFormulaManager(FormulaManager pDelegate, DebuggingContext pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingIntegerFormulaManager(delegate.getIntegerFormulaManager(), debugging);
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingRationalFormulaManager(delegate.getRationalFormulaManager(), debugging);
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingBooleanFormulaManager(delegate.getBooleanFormulaManager(), debugging);
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingArrayFormulaManager(delegate.getArrayFormulaManager(), debugging);
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), debugging);
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingFloatingPointFormulaManager(
        delegate.getFloatingPointFormulaManager(), debugging);
  }

  @Override
  public UFManager getUFManager() {
    debugging.assertThreadLocal();
    return new DebuggingUFManager(delegate.getUFManager(), debugging);
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingSLFormulaManager(delegate.getSLFormulaManager(), debugging);
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingQuantifiedFormulaManager(delegate.getQuantifiedFormulaManager(), debugging);
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingStringFormulaManager(delegate.getStringFormulaManager(), debugging);
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingEnumerationFormulaManager(
        delegate.getEnumerationFormulaManager(), debugging);
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    debugging.assertThreadLocal();
    T result = delegate.makeVariable(formulaType, name);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    debugging.assertThreadLocal();
    for (Formula f : args) {
      debugging.assertFormulaInContext(f);
    }
    T result = delegate.makeApplication(declaration, args);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    debugging.assertThreadLocal();
    for (Formula f : args) {
      debugging.assertFormulaInContext(f);
    }
    T result = delegate.makeApplication(declaration, args);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.getFormulaType(formula);
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.parse(s);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pT);
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
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(input);
    BooleanFormula result = delegate.applyTactic(input, tactic);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(input);
    T result = delegate.simplify(input);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    return delegate.visit(f, rFormulaVisitor);
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    return delegate.transformRecursively(f, pFormulaVisitor);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    return delegate.extractVariables(f);
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    return delegate.extractVariablesAndUFs(f);
  }

  @Override
  public <T extends Formula> T substitute(
      T f, Map<? extends Formula, ? extends Formula> fromToMapping) {
    debugging.assertThreadLocal();
    List<Formula> checkAll = new ArrayList<>();
    checkAll.add(f);
    checkAll.addAll(fromToMapping.keySet());
    checkAll.addAll(fromToMapping.values());
    for (Formula term : checkAll) {
      debugging.assertFormulaInContext(term);
    }
    T result = delegate.substitute(f, fromToMapping);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (otherManager instanceof DebuggingFormulaManager) {
      ((DebuggingFormulaManager) otherManager).debugging.assertFormulaInContext(formula);
    }
    BooleanFormula result = delegate.translateFrom(formula, otherManager);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public boolean isValidName(String variableName) {
    debugging.assertThreadLocal();
    return delegate.isValidName(variableName);
  }

  @Override
  public String escape(String variableName) {
    debugging.assertThreadLocal();
    return delegate.escape(variableName);
  }

  @Override
  public String unescape(String variableName) {
    debugging.assertThreadLocal();
    return delegate.unescape(variableName);
  }
}
