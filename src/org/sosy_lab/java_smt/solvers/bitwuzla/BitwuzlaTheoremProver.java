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
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Option;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Result;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Terminator;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

class BitwuzlaTheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {
  private final Terminator terminator =
      new Terminator() {
        @Override
        public boolean terminate() {
          return shutdownNotifier.shouldShutdown(); // shutdownNotifer is defined in the superclass
        }
      };
  private final Bitwuzla env;

  @SuppressWarnings("unused")
  private final BitwuzlaFormulaManager manager;

  private final BitwuzlaFormulaCreator creator;

  protected BitwuzlaTheoremProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      Options pSolverOptions) {
    super(pOptions, pManager.getBooleanFormulaManager(), pShutdownNotifier);
    manager = pManager;
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

    return new Bitwuzla(creator.getTermManager(), pSolverOptions);
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

  @Override
  public @Nullable Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    Term formula = creator.extractInfo(constraint);
    env.assert_formula(formula);
    for (Term t : creator.getConstraintsForTerm(formula)) {
      env.assert_formula(t);
    }
    return null;
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
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    Collection<Term> newAssumptions = new LinkedHashSet<>();
    for (BooleanFormula formula : assumptions) {
      Term term = creator.extractInfo(formula);
      newAssumptions.add(term);
      newAssumptions.addAll(creator.getConstraintsForTerm(term));
    }

    final Result result = env.check_sat(new Vector_Term(newAssumptions));
    return readSATResult(result);
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

  private List<BooleanFormula> getUnsatCore0() {
    List<BooleanFormula> wrapped = new ArrayList<>();
    for (Term term : env.get_unsat_core()) {
      wrapped.add(creator.encapsulateBoolean(term));
    }
    return wrapped;
  }

  /**
   * Get an unsat core. This should be called only immediately after an {@link #isUnsat()} call that
   * returned <code>false</code>.
   */
  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    return getUnsatCore0();
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
    changedSinceLastSatQuery = false;
    boolean sat = !isUnsatWithAssumptions(assumptions);
    return sat ? Optional.empty() : Optional.of(getUnsatCore0());
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
