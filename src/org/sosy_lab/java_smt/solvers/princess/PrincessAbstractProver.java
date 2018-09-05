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
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.INot;
import ap.parser.ITerm;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import scala.Enumeration.Value;
import scala.Option;

abstract class PrincessAbstractProver<E, AF> extends AbstractProver<E> {

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
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pOptions);
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
    if (trackingStack.isEmpty()) {
      oldConstraintNum = 0;
    } else {
      oldConstraintNum = trackingStack.peek().constraintNum;
    }
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
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    return new PrincessModel(api.partialModel(), creator);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (PrincessModel model = getModel()) {
      return model.modelToList();
    }
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Solving with assumptions is not supported.");
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    final List<BooleanFormula> result = new ArrayList<>();
    final scala.collection.immutable.Set<Object> core = api.getUnsatCore();

    int cnt = 0;
    for (IExpression formula : getAssertedFormulas()) {
      if (core.contains(cnt)) {
        result.add(mgr.encapsulateBooleanFormula(formula));
      }
      ++cnt;
    }
    return result;
  }

  protected abstract Iterable<IExpression> getAssertedFormulas();

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) {
    throw new UnsupportedOperationException("UNSAT cores not supported by Princess");
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

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // unpack formulas to terms
    List<IFormula> importantFormulas = new ArrayList<>(important.size());
    for (BooleanFormula impF : important) {
      importantFormulas.add((IFormula) mgr.extractInfo(impF));
    }

    api.push();
    while (!isUnsat()) {
      shutdownNotifier.shutdownIfNecessary();

      IFormula newFormula = new IBoolLit(true); // neutral element for AND
      List<BooleanFormula> wrappedPartialModel = new ArrayList<>(important.size());
      for (final IFormula f : importantFormulas) {
        final Option<Object> value = api.evalPartial(f);
        if (value.isDefined()) {
          final boolean isTrueValue = (boolean) value.get();
          final IFormula newElement = isTrueValue ? f : new INot(f);

          wrappedPartialModel.add(mgr.encapsulateBooleanFormula(newElement));
          newFormula = new IBinFormula(IBinJunctor.And(), newFormula, newElement);
        }
      }
      callback.apply(wrappedPartialModel);

      // add negation of current formula to get a new model in next iteration
      addConstraint0(new INot(newFormula));
    }
    shutdownNotifier.shutdownIfNecessary();
    api.pop();

    wasLastSatCheckSat = false; // we do not know about the current state, thus we reset the flag.

    return callback.getResult();
  }

  /** add external definition: boolean variable. */
  void addSymbol(IFormula f) {
    Preconditions.checkState(!closed);
    api.addBooleanVariable(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().booleanSymbols.add(f);
    }
  }

  /** add external definition: integer variable. */
  void addSymbol(ITerm f) {
    Preconditions.checkState(!closed);
    api.addConstant(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().intSymbols.add(f);
    }
  }

  /** add external definition: uninterpreted function. */
  void addSymbol(IFunction f) {
    Preconditions.checkState(!closed);
    api.addFunction(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().functionSymbols.add(f);
    }
  }

  private static class Level {
    final List<IFormula> booleanSymbols = new ArrayList<>();
    final List<ITerm> intSymbols = new ArrayList<>();
    final List<IFunction> functionSymbols = new ArrayList<>();
    // the number of constraints asserted up to this point, this is needed
    // for unsat core computation
    int constraintNum = 0;

    Level(int constraintNum) {
      this.constraintNum = constraintNum;
    }

    /** add higher level to current level, we keep the order of creating symbols. */
    void mergeWithHigher(Level other) {
      this.booleanSymbols.addAll(other.booleanSymbols);
      this.intSymbols.addAll(other.intSymbols);
      this.functionSymbols.addAll(other.functionSymbols);
    }

    @Override
    public String toString() {
      return String.format("{%s, %s, %s}", booleanSymbols, intSymbols, functionSymbols);
    }
  }
}
