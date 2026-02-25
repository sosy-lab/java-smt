// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.Lists;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Option;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Result;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Terminator;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

abstract class BitwuzlaAbstractProver<T> extends AbstractProverWithAllSat<T> {
  private final Terminator terminator =
      new Terminator() {
        @Override
        public boolean terminate() {
          return shutdownNotifier.shouldShutdown(); // shutdownNotifer is defined in the superclass
        }
      };
  private static final UniqueIdGenerator ID_GENERATOR = new UniqueIdGenerator();

  protected final Map<Integer, Term> stack = new HashMap<>();

  protected final BitwuzlaFormulaCreator creator;
  protected final Bitwuzla env;

  protected BitwuzlaAbstractProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      Options pSolverOptions) {
    super(pOptions, pManager.getBooleanFormulaManager(), pShutdownNotifier);
    creator = pCreator;

    // Bitwuzla guarantees that Terms and Sorts are shared
    env = createEnvironment(pOptions, pSolverOptions);

    // Install shutdown hook
    env.configure_terminator(terminator);
  }

  private Bitwuzla createEnvironment(Set<ProverOptions> pProverOptions, Options pSolverOptions) {
    if (pProverOptions.contains(ProverOptions.GENERATE_MODELS)
        || pProverOptions.contains(ProverOptions.GENERATE_ALL_SAT)) {
      pSolverOptions.set(Option.PRODUCE_MODELS, 2);
    }
    if (pProverOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      pSolverOptions.set(Option.PRODUCE_UNSAT_CORES, 2);
    }
    if (pProverOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      pSolverOptions.set(Option.PRODUCE_UNSAT_ASSUMPTIONS, 2);
    }

    return new Bitwuzla(creator.getEnv(), pSolverOptions);
  }

  @Override
  protected boolean hasPersistentModel() {
    return false;
  }

  /**
   * Remove one backtracking point/level from the current stack. This removes the latest level
   * including all of its formulas, i.e., all formulas that were added for this backtracking point.
   */
  @Override
  public void popImpl() {
    env.pop(1);
  }

  @CanIgnoreReturnValue
  protected int addConstraint0(BooleanFormula constraint) {
    Term formula = creator.extractInfo(constraint);
    for (Term t : creator.getConstraintsForTerm(formula)) {
      formula = creator.getEnv().mk_term(Kind.AND, formula, t);
    }
    env.assert_formula(formula);

    var label = BitwuzlaAbstractProver.ID_GENERATOR.getFreshId();
    stack.put(label, formula);
    return label;
  }

  /**
   * Create a new backtracking point, i.e., a new level on the assertion stack. Each level can hold
   * several asserted formulas.
   *
   * <p>If formulas are added before creating the first backtracking point, they can not be removed
   * via a POP-operation.
   */
  @Override
  public void pushImpl() throws InterruptedException {
    env.push(1);
  }

  private boolean readSATResult(Result resultValue) throws SolverException, InterruptedException {
    if (resultValue == Result.SAT) {
      return false;
    } else if (resultValue == Result.UNSAT) {
      return true;
    } else if (resultValue == Result.UNKNOWN && shutdownNotifier.shouldShutdown()) {
      throw new InterruptedException();
    } else {
      throw new SolverException("Bitwuzla returned UNKNOWN.");
    }
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException, InterruptedException {
    return readSATResult(env.check_sat());
  }

  /**
   * Check whether the conjunction of all formulas on the stack together with the list of
   * assumptions is satisfiable.
   *
   * @param assumptions A list of literals.
   */
  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions) {
    throw new UnsupportedOperationException();
  }

  /**
   * Get a satisfying assignment. This method should be called only immediately after an {@link
   * #isUnsat()} call that returned <code>false</code>. The returned model is guaranteed to stay
   * constant and valid as long as the solver context is available, even if constraints are added
   * to, pushed or popped from the prover stack.
   *
   * <p>A model might contain additional symbols with their evaluation, if a solver uses its own
   * temporary symbols. There should be at least a value-assignment for each free symbol.
   */
  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    checkGenerateModels();
    // special case for Bitwuzla: Models are not permanent and need to be closed
    // before any change is applied to the prover stack. So, we register the Model as Evaluator.
    return getEvaluatorWithoutChecks();
  }

  /**
   * Get an unsat core. This should be called only immediately after an {@link #isUnsat()} call that
   * returned <code>false</code>.
   */
  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    return Lists.transform(env.get_unsat_core(), creator::encapsulateBoolean);
  }

  /**
   * Returns an UNSAT core (if it exists, otherwise {@code Optional.empty()}), over the chosen
   * assumptions. Does NOT require the {@link ProverOptions#GENERATE_UNSAT_CORE} option to work.
   *
   * @param assumptions Selected assumptions
   * @return Empty optional if the constraints with assumptions are satisfiable, subset of
   *     assumptions which is unsatisfiable with the original constraints otherwise.
   */
  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Preconditions.checkNotNull(assumptions);
    checkGenerateUnsatCoresOverAssumptions();

    changedSinceLastSatQuery = true;

    Collection<Term> newAssumptions = new LinkedHashSet<>();
    for (BooleanFormula formula : assumptions) {
      Term term = creator.extractInfo(formula);
      newAssumptions.add(term);
      newAssumptions.addAll(creator.getConstraintsForTerm(term));
    }
    Result result = env.check_sat(new Vector_Term(newAssumptions));

    return !readSATResult(result)
        ? Optional.empty()
        : Optional.of(Lists.transform(env.get_unsat_assumptions(), creator::encapsulateBoolean));
  }

  /**
   * Closes the prover environment. The object should be discarded, and should not be used after
   * closing. The first call of this method will close the prover instance, further calls are
   * ignored.
   */
  @Override
  public void close() {
    if (!closed) {
      closed = true;
      env.close();
    }
    super.close();
  }

  @SuppressWarnings("resource")
  @Override
  protected BitwuzlaModel getEvaluatorWithoutChecks() {
    return registerEvaluator(
        new BitwuzlaModel(
            env,
            this,
            creator,
            Collections2.transform(getAssertedFormulas(), creator::extractInfo)));
  }

  public boolean isClosed() {
    return closed;
  }
}
