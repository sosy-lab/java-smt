// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This class is a utility-class to avoid repeated implementation of the AllSAT computation.
 *
 * <p>If a solver does not support direct AllSAT computation, please inherit from this class.
 */
public abstract class AbstractProverWithAllSat<T> extends AbstractProver<T> {

  protected final ShutdownNotifier shutdownNotifier;
  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;
  private final QuantifiedFormulaManager qfmgr;

  protected AbstractProverWithAllSat(
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      BooleanFormulaManager pBmgr,
      QuantifiedFormulaManager pQfmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    mgr = pMgr;
    bmgr = pBmgr;
    qfmgr = pQfmgr;
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> importantPredicates)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkGenerateAllSat();

    push();
    try {
      // try model-based computation of ALLSAT
      iterateOverAllModels(callback, importantPredicates);
    } catch (SolverException e) {
      // fallback to direct SAT/UNSAT-based computation of ALLSAT
      iterateOverAllPredicateCombinations(callback, importantPredicates, new ArrayDeque<>());
      // TODO should we completely switch to the second method?
    }

    pop();
    return callback.getResult();
  }

  /**
   * This method computes all satisfiable assignments for the given predicates by iterating over all
   * models. The SMT solver can choose the ordering of variables and shortcut model generation.
   */
  private <R> void iterateOverAllModels(
      AllSatCallback<R> callback, List<BooleanFormula> importantPredicates)
      throws SolverException, InterruptedException {
    while (!isUnsat()) {
      shutdownNotifier.shutdownIfNecessary();

      ImmutableList.Builder<BooleanFormula> valuesOfModel = ImmutableList.builder();
      try (Evaluator evaluator = getEvaluatorWithoutChecks()) {
        for (BooleanFormula formula : importantPredicates) {
          Boolean value = evaluator.evaluate(formula);
          if (value == null) {
            // This is a legal return value for evaluation.
            // The value doesn't matter. We ignore this assignment.
            // This step aim for shortcutting the ALLSAT-loop.
          } else if (value) {
            valuesOfModel.add(formula);
          } else {
            valuesOfModel.add(bmgr.not(formula));
          }
        }
      }

      final ImmutableList<BooleanFormula> values = valuesOfModel.build();
      callback.apply(values);
      shutdownNotifier.shutdownIfNecessary();

      BooleanFormula negatedModel = bmgr.not(bmgr.and(values));
      addConstraint(negatedModel);
      shutdownNotifier.shutdownIfNecessary();
    }
  }

  /**
   * This method computes all satisfiable assignments for the given predicates by (recursively)
   * traversing the decision tree over the given variables. The ordering of variables is fixed, and
   * we can only ignore unsatisfiable subtrees.
   *
   * <p>In contrast to {@link #iterateOverAllModels} we do not use model generation here, which is a
   * benefit for some solvers or theory combinations.
   *
   * @param predicates remaining predicates in the decision tree.
   * @param valuesOfModel already chosen predicate values, ordered as appearing in the tree.
   */
  private <R> void iterateOverAllPredicateCombinations(
      AllSatCallback<R> callback,
      List<BooleanFormula> predicates,
      Deque<BooleanFormula> valuesOfModel)
      throws SolverException, InterruptedException {

    shutdownNotifier.shutdownIfNecessary();

    if (isUnsat()) {
      return;

    } else if (predicates.isEmpty()) {
      // we aim at providing the same order of predicates as given as parameter, thus reverse.
      callback.apply(ImmutableList.copyOf(valuesOfModel).reverse());

    } else {

      // positive predicate
      final BooleanFormula predicate = predicates.get(0);
      valuesOfModel.push(predicate);
      push(predicate);
      iterateOverAllPredicateCombinations(
          callback, predicates.subList(1, predicates.size()), valuesOfModel);
      pop();
      valuesOfModel.pop();

      // negated predicate
      final BooleanFormula notPredicate = bmgr.not(predicates.get(0));
      valuesOfModel.push(notPredicate);
      push(notPredicate);
      iterateOverAllPredicateCombinations(
          callback, predicates.subList(1, predicates.size()), valuesOfModel);
      pop();
      valuesOfModel.pop();
    }
  }

  /**
   * Get an evaluator instance for model evaluation without executing checks for prover options.
   *
   * <p>This method allows model evaluation without explicitly enabling the prover-option {@link
   * ProverOptions#GENERATE_MODELS}. We only use this method internally, when we know about a valid
   * solver state. The returned evaluator does not have caching or any direct optimization for user
   * interaction.
   *
   * @throws SolverException if model can not be constructed.
   */
  protected abstract Evaluator getEvaluatorWithoutChecks() throws SolverException;
}
