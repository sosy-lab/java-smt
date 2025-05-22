// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class DebuggingBooleanFormulaManager implements BooleanFormulaManager {
  private final BooleanFormulaManager delegate;
  private final DebuggingAssertions debugging;

  DebuggingBooleanFormulaManager(BooleanFormulaManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BooleanFormula makeTrue() {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.makeTrue();
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula makeFalse() {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.makeFalse();
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.makeVariable(pVar);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula1);
    debugging.assertFormulaInContext(formula2);
    BooleanFormula result = delegate.equivalence(formula1, formula2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula1);
    debugging.assertFormulaInContext(formula2);
    BooleanFormula result = delegate.implication(formula1, formula2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public boolean isTrue(BooleanFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.isTrue(formula);
  }

  @Override
  public boolean isFalse(BooleanFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.isFalse(formula);
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(cond);
    debugging.assertFormulaInContext(f1);
    debugging.assertFormulaInContext(f2);
    T result = delegate.ifThenElse(cond, f1, f2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula not(BooleanFormula bits) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits);
    BooleanFormula result = delegate.not(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BooleanFormula result = delegate.and(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> bits) {
    debugging.assertThreadLocal();
    for (BooleanFormula f : bits) {
      debugging.assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.and(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula and(BooleanFormula... bits) {
    debugging.assertThreadLocal();
    for (BooleanFormula f : bits) {
      debugging.assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.and(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(
        Collectors.toList(),
        (terms) -> {
          for (BooleanFormula f : terms) {
            debugging.assertFormulaInContext(f);
          }
          BooleanFormula result = and(terms);
          debugging.addFormulaTerm(result);
          return result;
        });
  }

  @Override
  public BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BooleanFormula result = delegate.or(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> bits) {
    debugging.assertThreadLocal();
    for (BooleanFormula f : bits) {
      debugging.assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.or(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula or(BooleanFormula... bits) {
    debugging.assertThreadLocal();
    for (BooleanFormula f : bits) {
      debugging.assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.or(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(
        Collectors.toList(),
        (terms) -> {
          for (BooleanFormula f : terms) {
            debugging.assertFormulaInContext(f);
          }
          BooleanFormula result = or(terms);
          debugging.addFormulaTerm(result);
          return result;
        });
  }

  @Override
  public BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BooleanFormula result = delegate.xor(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pFormula);
    return delegate.visit(pFormula, visitor);
  }

  @Override
  public void visitRecursively(
      BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    BooleanFormula result = delegate.transformRecursively(f, pVisitor);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    Set<BooleanFormula> result = delegate.toConjunctionArgs(f, flatten);
    for (BooleanFormula r : result) {
      debugging.addFormulaTerm(r);
    }
    return result;
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    Set<BooleanFormula> result = delegate.toDisjunctionArgs(f, flatten);
    for (BooleanFormula r : result) {
      debugging.addFormulaTerm(r);
    }
    return result;
  }
}
