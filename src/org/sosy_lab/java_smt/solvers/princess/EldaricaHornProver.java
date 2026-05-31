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

import ap.CmdlMain.NullStream$;
import ap.api.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.Set;
import lazabs.horn.CEGARHornWrapper;
import lazabs.horn.HornAPI;
import lazabs.horn.HornWrapper;
import lazabs.horn.Util.Dag;
import lazabs.horn.abstractions.EmptyVerificationHints$;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.preprocessor.DefaultPreprocessor;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.princess.eldarica.PrincessHornConverter;
import scala.Function0;
import scala.collection.immutable.Map;
import scala.jdk.javaapi.CollectionConverters;
import scala.util.Either;

public class EldaricaHornProver extends PrincessAbstractProver<Void> implements
                                                                     HornProverEnvironment {
  private final HornAPI horn;
  private final ArrayList<Clause> clauses = new ArrayList<>();
  private final PrincessHornConverter converter = new PrincessHornConverter();

  public EldaricaHornProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
    this.horn = new HornAPI(new HornAPI.CEGAROptions()); // TODO: options
  }

  private void addConstraint1(BooleanFormula constraint) {
    Preconditions.checkState(!closed);

    final int formulaId = idGenerator.getFreshId();
    partitions.push(partitions.pop().putAndCopy(formulaId, constraint));
    api.setPartitionNumber(formulaId);

    final IFormula formula = (IFormula) mgr.extractInfo(constraint);
    // TODO: purpose?
    var assertion =
        api.abbrevSharedExpressions(formula, creator.getEnv().getMinAtomsForAbbreviation());

    if (assertion.isFalse()) {
      throw new RuntimeException("TODO: handle false");
    }
    if (assertion.isTrue()) {
      return;
    }

    var clause = converter.toClause(assertion);

    this.clauses.add(clause);
  }

  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    addConstraint1(constraint);
    return null;
  }

  private Either<Function0<Map<Predicate, IFormula>>, Function0<Dag<IAtom>>> solve() {
    var clauses = CollectionConverters.asScala(this.clauses).toSeq();
    var preprocessor = new DefaultPreprocessor();
    var preprocessed = preprocessor.process(clauses,EmptyVerificationHints$.MODULE$);

    var result = new CEGARHornWrapper(clauses, preprocessed._1(), preprocessed._2(),
        preprocessed._3(), false, System.err).result();


    return result;
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException {
    var result = solve();

    return result.isRight();
   // return !this.horn.isSat(CollectionConverters.asScala(this.clauses));
  }

  // TODO: Model, push/pop?.
}
