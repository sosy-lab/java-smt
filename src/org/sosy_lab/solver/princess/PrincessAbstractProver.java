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
package org.sosy_lab.solver.princess;

import static com.google.common.base.Preconditions.checkNotNull;
import static scala.collection.JavaConversions.iterableAsScalaIterable;

import ap.SimpleAPI;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.ITerm;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Model.ValueAssignment;

import scala.Enumeration.Value;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;

abstract class PrincessAbstractProver<E, AF> implements BasicProverEnvironment<E> {

  protected final SimpleAPI api;
  protected final PrincessFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>(); // all terms on all levels
  private final Deque<Level> trackingStack = new ArrayDeque<>(); // symbols on all levels
  protected final ShutdownNotifier shutdownNotifier;

  protected final PrincessFormulaCreator creator;
  protected boolean closed = false;

  protected PrincessAbstractProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier) {
    this.mgr = pMgr;
    this.creator = creator;
    this.api = checkNotNull(pApi);
    this.shutdownNotifier = checkNotNull(pShutdownNotifier);
  }

  /** This function causes the SatSolver to check all the terms on the stack,
   * if their conjunction is SAT or UNSAT.
   */
  @Override
  public boolean isUnsat() throws SolverException {
    Preconditions.checkState(!closed);
    final Value result = api.checkSat(true);
    if (result == SimpleAPI.ProverStatus$.MODULE$.Sat()) {
      return false;
    } else if (result == SimpleAPI.ProverStatus$.MODULE$.Unsat()) {
      return true;
    } else if (result == SimpleAPI.ProverStatus$.MODULE$.OutOfMemory()) {
      throw new SolverException(
          "Princess ran out of stack or heap memory, try increasing their sizes.");
    } else {
      throw new SolverException("Princess' checkSat call returned " + result);
    }
  }

  protected void addConstraint0(IFormula t) {
    Preconditions.checkState(!closed);
    api.addAssertion(
        api.abbrevSharedExpressions(
            t, creator.getEnv().princessOptions.getMinAtomsForAbbreviation()));
  }

  @Override
  public final void push() {
    Preconditions.checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    api.push();
    trackingStack.push(new Level());
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.pop();
    api.pop();

    // we have to recreate symbols on lower levels, because JavaSMT assumes "global" symbols.
    Level level = trackingStack.pop();
    api.addBooleanVariables(iterableAsScalaIterable(level.booleanSymbols));
    api.addConstants(iterableAsScalaIterable(level.intSymbols));
    level.functionSymbols.forEach(api::addFunction);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().mergeWithHigher(level);
    }
  }

  @Override
  public PrincessModel getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!isUnsat(), "model is only available for SAT environments");
    return new PrincessModel(api.partialModel(), creator);
  }

  protected abstract Collection<? extends IExpression> getAssertedFormulas();

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (PrincessModel model = getModel()) {
      return model.modelToList();
    }
  }

  @SuppressWarnings("unused")
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Assumption-solving is not supported.");
  }

  /**
   * Clean the stack, such that it can be re-used.
   * The caller has to guarantee, that a stack not used by several provers
   * after calling {@link #close()}, because there is a dependency
   * from 'one' prover to 'one' (reusable)
   */
  @Override
  public void close() {
    checkNotNull(api);
    checkNotNull(mgr);
    if (!closed) {
      if (shutdownNotifier.shouldShutdown()) {
        creator.getEnv().removeStack(this, api);
        api.shutDown();
      } else {
        for (int i = 0; i < trackingStack.size(); i++) {
          pop();
        }
        creator.getEnv().unregisterStack(this, api);
      }
    }
    closed = true;
  }

  /** add external definition: boolean variable. */
  void addSymbol(IFormula f) {
    Preconditions.checkState(!closed);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().booleanSymbols.add(f);
    }
  }

  /** add external definition: integer variable. */
  void addSymbol(ITerm f) {
    Preconditions.checkState(!closed);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().intSymbols.add(f);
    }
  }

  /** add external definition: uninterpreted function. */
  void addSymbol(IFunction f) {
    Preconditions.checkState(!closed);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().functionSymbols.add(f);
    }
  }

  private static class Level {
    List<IFormula> booleanSymbols = new ArrayList<>();
    List<ITerm> intSymbols = new ArrayList<>();
    List<IFunction> functionSymbols = new ArrayList<>();

    /**  add higher level to current level, we keep the order of creating symbols. */
    void mergeWithHigher(Level other) {
      this.booleanSymbols.addAll(other.booleanSymbols);
      this.intSymbols.addAll(other.intSymbols);
      this.functionSymbols.addAll(other.functionSymbols);
    }
  }
}
