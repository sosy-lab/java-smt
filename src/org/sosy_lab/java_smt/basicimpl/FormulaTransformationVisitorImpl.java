// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

/** Internal implementation of recursive transformation. */
final class FormulaTransformationVisitorImpl implements FormulaVisitor<Void> {

  private final Deque<Formula> toProcess;
  private final Map<Formula, Formula> pCache;
  private final FormulaVisitor<? extends Formula> delegate;

  FormulaTransformationVisitorImpl(
      FormulaVisitor<? extends Formula> delegate,
      Deque<Formula> toProcess,
      Map<Formula, Formula> pCache) {
    this.toProcess = Preconditions.checkNotNull(toProcess);
    this.pCache = Preconditions.checkNotNull(pCache);
    this.delegate = Preconditions.checkNotNull(delegate);
  }

  @Override
  public Void visitFreeVariable(Formula f, String name) {
    pCache.put(f, delegate.visitFreeVariable(f, name));
    return null;
  }

  @Override
  public Void visitBoundVariable(Formula f, int deBruijnIdx) {
    Preconditions.checkNotNull(f);

    // Bound variable transformation is not allowed.
    pCache.put(f, f);
    return null;
  }

  @Override
  public Void visitConstant(Formula f, Object value) {
    Preconditions.checkNotNull(f);
    pCache.put(f, delegate.visitConstant(f, value));
    return null;
  }

  @Override
  public Void visitFunction(
      Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
    Preconditions.checkNotNull(f);

    boolean allArgumentsTransformed = true;

    // Construct a new argument list for the function application.
    List<Formula> newArgs = new ArrayList<>(args.size());

    for (Formula c : args) {
      Formula newC = pCache.get(c);

      if (newC != null) {
        newArgs.add(newC);
      } else {
        toProcess.push(c);
        allArgumentsTransformed = false;
      }
    }

    // The Flag childrenDone indicates whether all arguments
    // of the function were already processed.
    if (allArgumentsTransformed) {

      // Create a processed version of the function application.
      if (!toProcess.isEmpty()) {
        toProcess.pop();
      }
      Formula out = delegate.visitFunction(f, newArgs, functionDeclaration);
      Formula prev = pCache.put(f, out);
      assert prev == null;
    }
    return null;
  }

  @Override
  public Void visitQuantifier(
      BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body)
      throws IOException {
    Preconditions.checkNotNull(f);
    Preconditions.checkNotNull(quantifier);
    Preconditions.checkNotNull(boundVariables);
    Preconditions.checkNotNull(body);

    BooleanFormula transformedBody = (BooleanFormula) pCache.get(body);

    if (transformedBody != null) {
      BooleanFormula newTt =
          (BooleanFormula) delegate.visitQuantifier(f, quantifier, boundVariables, transformedBody);
      pCache.put(f, newTt);

    } else {
      toProcess.push(body);
    }
    return null;
  }
}
