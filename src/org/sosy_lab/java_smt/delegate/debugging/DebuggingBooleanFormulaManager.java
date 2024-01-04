// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

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

public class DebuggingBooleanFormulaManager extends FormulaChecks implements BooleanFormulaManager {
  private final BooleanFormulaManager delegate;

  public DebuggingBooleanFormulaManager(
      BooleanFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula makeTrue() {
    assertThreadLocal();
    BooleanFormula result = delegate.makeTrue();
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula makeFalse() {
    assertThreadLocal();
    BooleanFormula result = delegate.makeFalse();
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    assertThreadLocal();
    BooleanFormula result = delegate.makeVariable(pVar);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2) {
    assertThreadLocal();
    assertFormulaInContext(formula1);
    assertFormulaInContext(formula2);
    BooleanFormula result = delegate.equivalence(formula1, formula2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2) {
    assertThreadLocal();
    assertFormulaInContext(formula1);
    assertFormulaInContext(formula2);
    BooleanFormula result = delegate.implication(formula1, formula2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public boolean isTrue(BooleanFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.isTrue(formula);
  }

  @Override
  public boolean isFalse(BooleanFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.isFalse(formula);
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2) {
    assertThreadLocal();
    assertFormulaInContext(cond);
    assertFormulaInContext(f1);
    assertFormulaInContext(f2);
    T result = delegate.ifThenElse(cond, f1, f2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula not(BooleanFormula bits) {
    assertThreadLocal();
    assertFormulaInContext(bits);
    BooleanFormula result = delegate.not(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BooleanFormula result = delegate.and(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> bits) {
    assertThreadLocal();
    for (BooleanFormula f : bits) {
      assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.and(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula and(BooleanFormula... bits) {
    assertThreadLocal();
    for (BooleanFormula f : bits) {
      assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.and(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(
        Collectors.toList(),
        (terms) -> {
          for (BooleanFormula f : terms) {
            assertFormulaInContext(f);
          }
          BooleanFormula result = and(terms);
          addFormulaToContext(result);
          return result;
        });
  }

  @Override
  public BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BooleanFormula result = delegate.or(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> bits) {
    assertThreadLocal();
    for (BooleanFormula f : bits) {
      assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.or(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula or(BooleanFormula... bits) {
    assertThreadLocal();
    for (BooleanFormula f : bits) {
      assertFormulaInContext(f);
    }
    BooleanFormula result = delegate.or(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(
        Collectors.toList(),
        (terms) -> {
          for (BooleanFormula f : terms) {
            assertFormulaInContext(f);
          }
          BooleanFormula result = or(terms);
          addFormulaToContext(result);
          return result;
        });
  }

  @Override
  public BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BooleanFormula result = delegate.xor(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    assertThreadLocal();
    assertFormulaInContext(pFormula);
    return delegate.visit(pFormula, visitor);
  }

  @Override
  public void visitRecursively(
      BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor) {
    assertThreadLocal();
    assertFormulaInContext(f);
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    assertThreadLocal();
    assertFormulaInContext(f);
    BooleanFormula result = delegate.transformRecursively(f, pVisitor);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    assertThreadLocal();
    assertFormulaInContext(f);
    Set<BooleanFormula> result = delegate.toConjunctionArgs(f, flatten);
    for (BooleanFormula r : result) {
      addFormulaToContext(r);
    }
    return result;
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    assertThreadLocal();
    assertFormulaInContext(f);
    Set<BooleanFormula> result = delegate.toDisjunctionArgs(f, flatten);
    for (BooleanFormula r : result) {
      addFormulaToContext(r);
    }
    return result;
  }
}
