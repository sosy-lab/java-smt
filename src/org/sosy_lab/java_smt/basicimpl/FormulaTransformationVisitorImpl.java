/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;

/**
 * Internal implementation of recursive transformation.
 */
final class FormulaTransformationVisitorImpl implements FormulaVisitor<Void> {

  private final Deque<Formula> toProcess;
  private final Map<Formula, Formula> pCache;
  private final FormulaVisitor<? extends Formula> delegate;

  FormulaTransformationVisitorImpl(
      FormulaVisitor<? extends Formula> delegate,
      Deque<Formula> toProcess,
      Map<Formula, Formula> pCache) {
    this.toProcess = toProcess;
    this.pCache = pCache;
    this.delegate = Preconditions.checkNotNull(delegate);
  }

  @Override
  public Void visitFreeVariable(Formula f, String name) {
    pCache.put(f, delegate.visitFreeVariable(f, name));
    return null;
  }

  @Override
  public Void visitBoundVariable(Formula f, int deBruijnIdx) {

    // Bound variable transformation is not allowed.
    pCache.put(f, f);
    return null;
  }

  @Override
  public Void visitConstant(Formula f, Object value) {
    pCache.put(f, delegate.visitConstant(f, value));
    return null;
  }

  @Override
  public Void visitFunction(
      Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {

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

      // Create an processed version of the
      // function application.
      toProcess.pop();
      Formula out = delegate.visitFunction(f, newArgs, functionDeclaration);
      Formula prev = pCache.put(f, out);
      assert prev == null;
    }
    return null;
  }

  @Override
  public Void visitQuantifier(
      BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body) {
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
