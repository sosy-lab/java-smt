// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkNotNull;
import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.asScala;

import ap.api.PartialModel;
import ap.api.SimpleAPI;
import ap.api.SimpleAPI.SimpleAPIException;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.ITerm;
import com.google.common.base.Preconditions;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import scala.Enumeration.Value;

@SuppressWarnings("ClassTypeParameterName")
abstract class PrincessAbstractProver<E, AF> extends AbstractProverWithAllSat<E> {

  protected final SimpleAPI api;
  protected final PrincessFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>(); // all terms on all levels
  private final Deque<Level> trackingStack = new ArrayDeque<>(); // symbols on all levels

  private final PrincessFormulaCreator creator;
  protected boolean wasLastSatCheckSat = false; // and stack is not changed

  protected PrincessAbstractProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);
    this.mgr = pMgr;
    this.creator = creator;
    this.api = checkNotNull(pApi);

    assertedFormulas.push(new ArrayList<>());
    trackingStack.push(new Level(0));
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
    Preconditions.checkState(size() > 0);
    wasLastSatCheckSat = false;
    assertedFormulas.pop();
    api.pop();

    // we have to recreate symbols on lower levels, because JavaSMT assumes "global" symbols.
    Level level = trackingStack.pop();
    api.addBooleanVariables(asScala(level.booleanSymbols));
    api.addConstants(asScala(level.intSymbols));
    level.functionSymbols.forEach(api::addFunction);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().mergeWithHigher(level);
    }
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    return assertedFormulas.size() - 1;
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected PrincessModel getEvaluatorWithoutChecks() throws SolverException {
    final PartialModel partialModel;
    try {
      partialModel = partialModel();
    } catch (SimpleAPIException ex) {
      throw new SolverException(ex.getMessage(), ex);
    }
    return new PrincessModel(this, partialModel, creator, api);
  }

  /**
   * This method only exists to allow catching the exception from Scala in Java.
   *
   * @throws SimpleAPIException if model can not be constructed.
   */
  private PartialModel partialModel() throws SimpleAPIException {
    return api.partialModel();
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
    final Set<Object> core = asJava(api.getUnsatCore());

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
    throw new UnsupportedOperationException(
        "UNSAT cores over assumptions not supported by Princess");
  }

  @Override
  public void close() {
    checkNotNull(api);
    checkNotNull(mgr);
    if (!closed) {
      api.shutDown();
      api.reset(); // cleanup memory, even if we keep a reference to "api" and "mgr"
      creator.getEnv().unregisterStack(this);
    }
    closed = true;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    T result = super.allSat(callback, important);
    wasLastSatCheckSat = false; // we do not know about the current state, thus we reset the flag.
    return result;
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
    int constraintNum;

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
