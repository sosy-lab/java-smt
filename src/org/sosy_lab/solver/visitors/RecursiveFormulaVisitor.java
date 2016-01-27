/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.visitors;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * Formula visitor which visits every element exactly once.
 *
 * <p>Allows to traverse DAG-like formulas without an exponential explosion.
 */
public abstract class RecursiveFormulaVisitor implements FormulaVisitor<Void> {
  private final FormulaManager fmgr;
  private final Set<Formula> seen = new HashSet<>();
  private final Deque<Formula> toVisit = new LinkedList<>();

  protected RecursiveFormulaVisitor(FormulaManager pFmgr) {
    fmgr = checkNotNull(pFmgr);
  }

  public final Void visit(Formula f) {
    toVisit.add(f);
    while (!toVisit.isEmpty()) {
      Formula c = toVisit.pop();
      if (seen.add(c)) {
        fmgr.visit(this, c);
      }
    }
    return null;
  }

  @Override
  public Void visitFreeVariable(Formula f, String name) {
    return null;
  }

  @Override
  public Void visitBoundVariable(Formula f, int deBruijnIdx) {
    return null;
  }

  @Override
  public Void visitConstant(Formula f, Object value) {
    return null;
  }

  @Override
  public Void visitFunction(
      Formula f,
      List<Formula> args,
      FunctionDeclaration functionDeclaration,
      Function<List<Formula>, Formula> newApplicationConstructor) {
    for (Formula arg : args) {
      toVisit.add(arg);
    }
    return null;
  }

  @Override
  public Void visitQuantifier(
      BooleanFormula f, Quantifier q, List<Formula> boundVars, BooleanFormula body) {
    toVisit.add(body);
    return null;
  }
}
