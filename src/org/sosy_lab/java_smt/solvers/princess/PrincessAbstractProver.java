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
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.ITerm;
import ap.proof.certificates.Certificate;
import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import scala.Enumeration.Value;

@SuppressWarnings("ClassTypeParameterName")
abstract class PrincessAbstractProver<E> extends AbstractProverWithAllSat<E> {

  protected final SimpleAPI api;
  protected final PrincessFormulaManager mgr;
  protected final Deque<Level> trackingStack = new ArrayDeque<>(); // symbols on all levels

  /**
   * Values returned by {@link Model#evaluate(Formula)}.
   *
   * <p>We need to record these to make sure that the values returned by the evaluator are
   * consistant. Calling {@link #isUnsat()} will reset this list as the underlying model has been
   * updated.
   */
  protected final Set<IFormula> evaluatedTerms = new LinkedHashSet<>();

  // assign a unique partition number for eah added constraint, for unsat-core and interpolation.
  protected final UniqueIdGenerator idGenerator = new UniqueIdGenerator();
  protected final Deque<PersistentMap<Integer, BooleanFormula>> partitions = new ArrayDeque<>();

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

    trackingStack.push(new Level());
    partitions.push(PathCopyingPersistentTreeMap.of());
  }

  /**
   * This function causes the SatSolver to check all the terms on the stack, if their conjunction is
   * SAT or UNSAT.
   */
  @Override
  public boolean isUnsat() throws SolverException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    evaluatedTerms.clear();
    final Value result = api.checkSat(true);
    if (result.equals(SimpleAPI.ProverStatus$.MODULE$.Sat())) {
      wasLastSatCheckSat = true;
      evaluatedTerms.add(api.partialModelAsFormula());
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

  @CanIgnoreReturnValue
  protected int addConstraint0(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;

    final int formulaId = idGenerator.getFreshId();
    partitions.push(partitions.pop().putAndCopy(formulaId, constraint));
    api.setPartitionNumber(formulaId);

    final IFormula t = (IFormula) mgr.extractInfo(constraint);
    api.addAssertion(api.abbrevSharedExpressions(t, creator.getEnv().getMinAtomsForAbbreviation()));

    return formulaId;
  }

  @Override
  protected final void pushImpl() {
    wasLastSatCheckSat = false;
    api.push();
    trackingStack.push(new Level());
    partitions.push(partitions.peek());
  }

  @Override
  protected void popImpl() {
    wasLastSatCheckSat = false;
    api.pop();

    // we have to recreate symbols on lower levels, because JavaSMT assumes "global" symbols.
    Level level = trackingStack.pop();
    api.addBooleanVariables(asScala(level.booleanSymbols));
    api.addConstants(asScala(level.theorySymbols));
    level.functionSymbols.forEach(api::addFunction);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().mergeWithHigher(level);
    }
    partitions.pop();
  }

  /**
   * Get all terms that have been evaluated in the current model. The formulas are assignments that
   * extend the original model.
   */
  Collection<IFormula> getEvaluatedTerms() {
    return Collections.unmodifiableCollection(evaluatedTerms);
  }

  /** Track an assignment `term == value` for an evaluated term and its value. */
  void addEvaluatedTerm(IFormula pFormula) {
    evaluatedTerms.add(pFormula);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @SuppressWarnings("resource")
  @Override
  protected PrincessModel getEvaluatorWithoutChecks() throws SolverException {
    final PartialModel partialModel;
    try {
      partialModel = partialModel();
    } catch (SimpleAPIException ex) {
      throw new SolverException(ex.getMessage(), ex);
    }
    return registerEvaluator(new PrincessModel(this, partialModel, creator, api));
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
    for (Object partitionId : core) {
      result.add(partitions.peek().get(partitionId));
    }
    return result;
  }

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
      partitions.clear();
    }
    super.close();
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

  /** add external definition: theory variable (integer, rational, string, etc). */
  void addSymbol(ITerm f) {
    Preconditions.checkState(!closed);
    api.addConstant(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().theorySymbols.add(f);
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

  static class Level {
    final List<IFormula> booleanSymbols = new ArrayList<>();
    final List<ITerm> theorySymbols = new ArrayList<>();
    final List<IFunction> functionSymbols = new ArrayList<>();

    Level() {}

    /** add higher level to current level, we keep the order of creating symbols. */
    void mergeWithHigher(Level other) {
      this.booleanSymbols.addAll(other.booleanSymbols);
      this.theorySymbols.addAll(other.theorySymbols);
      this.functionSymbols.addAll(other.functionSymbols);
    }

    @Override
    public String toString() {
      return String.format("{%s, %s, %s}", booleanSymbols, theorySymbols, functionSymbols);
    }
  }

  //@Override
  //public ProofNode getProof() {
  //  api.getCertificate();
  //  return null;
 // }

 // protected Certificate getCertificate() {
 //   return api.getCertificate();
  //}
}
