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
package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkNotNull;
import static scala.collection.JavaConversions.iterableAsScalaIterable;

import ap.SimpleAPI;
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.ITerm;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import scala.Enumeration.Value;

abstract class PrincessAbstractProver<E, AF> implements BasicProverEnvironment<E> {

  protected final SimpleAPI api;
  protected final PrincessFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>(); // all terms on all levels
  private final Deque<Level> trackingStack = new ArrayDeque<>(); // symbols on all levels
  protected final ShutdownNotifier shutdownNotifier;

  private final PrincessFormulaCreator creator;
  protected boolean closed = false;
  protected boolean wasLastSatCheckSat = false; // and stack is not changed

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

  /**
   * This function causes the SatSolver to check all the terms on the stack, if their conjunction is
   * SAT or UNSAT.
   */
  @Override
  public boolean isUnsat() throws SolverException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    final Value result = api.checkSat(true);
    if (result.equals(SimpleAPI.ProverStatus$.MODULE$.Sat())) {
      wasLastSatCheckSat = true;
      return false;
    } else if (result.equals(SimpleAPI.ProverStatus$.MODULE$.Unsat())) {
      return true;
    } else if (result.equals(SimpleAPI.ProverStatus$.MODULE$.OutOfMemory())) {
      throw new SolverException(
          "Princess ran out of stack or heap memory, try increasing their sizes.");
    } else {
      throw new SolverException("Princess' checkSat call returned " + result);
    }
  }

  protected void addConstraint0(IFormula t) {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    api.addAssertion(api.abbrevSharedExpressions(t, creator.getEnv().getMinAtomsForAbbreviation()));
  }

  protected int addAssertedFormula(AF f) {
    assertedFormulas.peek().add(f);
    final int id = trackingStack.peek().constraintNum++;
    return id;
  }

  @Override
  public final void push() {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    assertedFormulas.push(new ArrayList<>());
    api.push();

    final int oldConstraintNum;
    if (trackingStack.isEmpty())
      oldConstraintNum = 0;
    else
      oldConstraintNum = trackingStack.peek().constraintNum;
    trackingStack.push(new Level(oldConstraintNum));
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
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
    Preconditions.checkState(wasLastSatCheckSat, "model is only available for SAT environments");
    return new PrincessModel(api.partialModel(), creator);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (PrincessModel model = getModel()) {
      return model.modelToList();
    }
  }

  @SuppressWarnings("unused")
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Solving with assumptions is not supported.");
  }

  /**
   * Clean the stack, such that it can be re-used. The caller has to guarantee, that a stack not
   * used by several provers after calling {@link #close()}, because there is a dependency from
   * 'one' prover to 'one' (reusable)
   */
  @Override
  public void close() {
    checkNotNull(api);
    checkNotNull(mgr);
    if (!closed) {
      if (shutdownNotifier.shouldShutdown()) {
        api.shutDown();
      } else {
        for (int i = 0; i < trackingStack.size(); i++) {
          pop();
        }
      }
      creator.getEnv().unregisterStack(this);
    }
    closed = true;
  }

  /** add external definition: boolean variable. */
  void addSymbol(IFormula f) {
    Preconditions.checkState(!closed);
    api.addBooleanVariable(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().booleanSymbols.add(f);
    }
  }

  /** add external definition: integer variable. */
  void addSymbol(ITerm f) {
    Preconditions.checkState(!closed);
    api.addConstant(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().intSymbols.add(f);
    }
  }

  /** add external definition: uninterpreted function. */
  void addSymbol(IFunction f) {
    Preconditions.checkState(!closed);
    api.addFunction(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().functionSymbols.add(f);
    }
  }

  private static class Level {
    final List<IFormula> booleanSymbols = new ArrayList<>();
    final List<ITerm> intSymbols = new ArrayList<>();
    final List<IFunction> functionSymbols = new ArrayList<>();
    // the number of constraints asserted up to this point, this is needed
    // for unsat core computation
    int constraintNum = 0;

    public Level(int constraintNum) {
      this.constraintNum = constraintNum;
    }

    /** add higher level to current level, we keep the order of creating symbols. */
    void mergeWithHigher(Level other) {
      this.booleanSymbols.addAll(other.booleanSymbols);
      this.intSymbols.addAll(other.intSymbols);
      this.functionSymbols.addAll(other.functionSymbols);
    }
  }
}
