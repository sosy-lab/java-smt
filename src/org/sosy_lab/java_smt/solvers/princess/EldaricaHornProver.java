/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;

import ap.api.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import com.google.common.base.Preconditions;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import lazabs.GlobalParameters;
import lazabs.horn.CEGARHornWrapper;
import lazabs.horn.Util.Dag;
import lazabs.horn.Util.NullStream$;
import lazabs.horn.abstractions.EmptyVerificationHints$;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.preprocessor.DefaultPreprocessor;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.princess.eldarica.PrincessHornConverter;
import scala.Console$;
import scala.Function0;
import scala.collection.JavaConverters;
import scala.collection.immutable.Map;
import scala.jdk.javaapi.CollectionConverters;
import scala.util.Either;

public class EldaricaHornProver extends PrincessAbstractProver<Void>
    implements HornProverEnvironment {
  private final ArrayList<Clause> clauses = new ArrayList<>();
  private final PrincessHornConverter converter = new PrincessHornConverter();

  @Nullable
  private Either<Function0<Map<Predicate, IFormula>>, Function0<Dag<IAtom>>> result = null;

  private static final boolean DEBUG_LOGGING = "true".equals(System.getenv("ELDARICA_DEBUG"));


  static {
    if (DEBUG_LOGGING) {
      GlobalParameters.get().setLogLevel(3);
      GlobalParameters.get().log_$eq(true);
    } else {
      GlobalParameters.get().setLogLevel(0);
      GlobalParameters.get().log_$eq(false);
    }
  }


  public EldaricaHornProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
  }


  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) {
    Preconditions.checkState(!closed);

    final IFormula formula = (IFormula) mgr.extractInfo(constraint);

    if (formula.isFalse()) {
      throw new RuntimeException("TODO: handle false");
    }
    if (formula.isTrue()) {
      return null;
    }

    var clause = converter.toClause(formula);

    this.clauses.add(clause);

    return null;
  }

  /**
   * Passes all clauses to Eldarica and solves it
   * @return Either (left) a model if sat, otherwise (right) a counter example.
   */
  private Either<Function0<Map<Predicate, IFormula>>, Function0<Dag<IAtom>>> solve() {
    if (this.result != null) {
      return this.result;
    }
    var stream = DEBUG_LOGGING ? System.err : new PrintStream(NullStream$.MODULE$);

    var err = Console$.MODULE$.err();
    try {
      Console$.MODULE$.setErrDirect(stream);

      var clauses = CollectionConverters.asScala(this.clauses).toSeq();
      var preprocessor = new DefaultPreprocessor();
      var preprocessed = preprocessor.process(clauses, EmptyVerificationHints$.MODULE$);

      var wrapper = new CEGARHornWrapper(clauses, preprocessed._1(), preprocessed._2(),
          preprocessed._3(), false, stream);

      var result = wrapper.result();


      this.result = result;
      return result;
    } finally {
      Console$.MODULE$.setErrDirect(err);
    }
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException {
    return solve().isRight();
  }

  @Override
  protected void setChanged() {
    result = null;
  }

  @Override
  public Model getModelImpl() throws SolverException {
    Map<Predicate, IFormula> model = solve().left().get().apply();

    return new EldaricaModel(JavaConverters.asJava(model), this, creator);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions) {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  protected boolean hasPersistentModel() {
    return false;
  }

  @Override
  public @Nullable Void push(BooleanFormula f) throws InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  protected void popImpl() {
    throw new UnsupportedOperationException();
  }

  @Override
  protected PrincessModel getEvaluatorWithoutChecks() throws SolverException {
    throw new UnsupportedOperationException();
  }
}
