// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.sri.yices.Config;
import com.sri.yices.Context;
import com.sri.yices.Parameters;
import com.sri.yices.Status;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;

/**
 * Info about the option {@link ProverOptions#GENERATE_UNSAT_CORE}: Yices provides the unsat core
 * only for additional formulae, not for already asserted ones. Thus, we have two possible
 * solutions:
 *
 * <p>1) Avoid incremental solving and simply provide all formulae as additional ones. Currently
 * implemented this way.
 *
 * <p>2) Add additional boolean symbols 'p', add a constraint 'p=f' for each asserted formula 'f',
 * compute the unsat core over all 'p's, and match them back to their formula 'f'. This allows
 * incremental solving, but is more complex to implement. Let's keep this idea is future work for
 * optimization.
 */
abstract class Yices2AbstractProver<T> extends AbstractProverWithAllSat<T>
    implements BasicProverEnvironment<T> {

  static final Parameters DEFAULT_PARAMS = new Parameters(); // use default setting in the solver

  protected final Yices2FormulaCreator creator;
  protected final Context curEnv;

  // Yices does not allow to PUSH when the stack is UNSAT.
  // Therefore, we need to keep track of all added constraints beyond that stack-level.
  private int stackSizeToUnsat = Integer.MAX_VALUE;

  private static final UniqueIdGenerator ID_GENERATOR = new UniqueIdGenerator();

  protected final Deque<PersistentMap<Integer, Integer>> stack = new ArrayDeque<>();

  Yices2AbstractProver(
      Yices2FormulaCreator pCreator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      String pSolverType) {
    super(pOptions, pBmgr, pShutdownNotifier);
    creator = pCreator;
    curEnv = newContext(pSolverType);
    stack.push(PathCopyingPersistentTreeMap.of());
  }

  boolean isClosed() {
    return closed;
  }

  @Override
  protected boolean hasPersistentModel() {
    return true;
  }

  Context newContext(String solverType) {
    try (var cfg = new Config()) {
      cfg.set("solver-type", solverType);
      cfg.set("mode", "interactive");
      cfg.set("model-interpolation", "true");
      return new Context(cfg);
    }
  }

  @SuppressWarnings("try")
  static boolean satCheckWithShutdownNotifier(
      Supplier<Status> satCheck, Context pCtx, ShutdownNotifier shutdownNotifier)
      throws InterruptedException, SolverException {
    try (ShutdownHook hook = new ShutdownHook(shutdownNotifier, pCtx::stopSearch)) {
      shutdownNotifier.shutdownIfNecessary();
      Status result = satCheck.get(); // the expensive computation
      shutdownNotifier.shutdownIfNecessary();

      return switch (result) {
        case SAT -> true;
        case UNSAT -> false;
        case INTERRUPTED -> throw new InterruptedException();
        case UNKNOWN -> throw new SolverException("SAT check returned \"unknown\"");
        default -> throw new SolverException("Internal solver exception");
      };
    }
  }

  @Override
  protected void popImpl() {
    if (size() < stackSizeToUnsat) { // constraintStack and Yices stack have same level.
      curEnv.pop();
      // Reset stackSizeToUnsat to bring the stack into a pushable state if it was UNSAT before.
      stackSizeToUnsat = Integer.MAX_VALUE;
    }
    stack.removeLast();
  }

  @CanIgnoreReturnValue
  protected int addConstraint0(BooleanFormula constraint) {
    var formula = creator.extractInfo(constraint);
    var label = Yices2AbstractProver.ID_GENERATOR.getFreshId();
    if (!generateUnsatCores) {
      // Skip adding the assertion if we plan to use getUnsatCore. We'll later use assumptions
      // solving to calculate an unsat core for the assertions
      curEnv.assertFormula(formula);
    }
    stack.addLast(stack.removeLast().putAndCopy(label, formula));
    return label;
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    if (size() < stackSizeToUnsat && curEnv.getStatus() != Status.UNSAT) {
      // Ensure that constraintStack and Yices stack are on the same level
      // and Context is not UNSAT from assertions since last push.
      curEnv.push();
    } else if (stackSizeToUnsat == Integer.MAX_VALUE) {
      // if previous check fails and stackSizeToUnsat is
      // not already set, set it to the current stack-size before pushing.
      stackSizeToUnsat = size();
    }
    stack.addLast(stack.getLast());
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException, InterruptedException {
    boolean unsat;
    if (generateUnsatCores) {
      // Yices only tracks assumptions for unsat core. We keep the stack empty and then treat all
      // assertions as assumptions while checking. If the result is 'unsat', we can then
      // calculate an unsat core
      unsat =
          !satCheckWithShutdownNotifier(
              () -> curEnv.checkWithAssumptions(DEFAULT_PARAMS, getAllConstraints()),
              curEnv,
              shutdownNotifier);

    } else {
      unsat =
          !satCheckWithShutdownNotifier(
              () -> curEnv.check(DEFAULT_PARAMS), curEnv, shutdownNotifier);

      if (unsat && stackSizeToUnsat == Integer.MAX_VALUE) {
        stackSizeToUnsat = size();
        // If sat check is UNSAT and stackSizeToUnsat waS not already set,
        // set to current constraintStack size.
      }
    }
    return unsat;
  }

  private int[] getAllConstraints() {
    return getAssertedFormulas().stream()
        .map(creator::extractInfo)
        .distinct()
        .mapToInt(Integer::intValue)
        .toArray();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkNotNull(pAssumptions);
    changedSinceLastSatQuery = false;
    wasLastSatCheckSatisfiable = false;

    final boolean isUnsat =
        !satCheckWithShutdownNotifier(
            () -> curEnv.checkWithAssumptions(DEFAULT_PARAMS, uncapsulate(pAssumptions)),
            curEnv,
            shutdownNotifier);
    if (!isUnsat) {
      wasLastSatCheckSatisfiable = true;
    }
    return isUnsat;
  }

  @SuppressWarnings("resource")
  @Override
  protected Model getModelImpl() throws SolverException {
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @SuppressWarnings("resource")
  @Override
  protected Yices2Model getEvaluatorWithoutChecks() {
    if (generateUnsatCores) {
      // We didn't push the assertions when we were planning to use getUnsatCore. Because of that
      // the SAT check now needs to be repeated to get a model
      curEnv.push();
      curEnv.assertFormulas(getAllConstraints());
      curEnv.check();
      var model = curEnv.getModel();
      curEnv.pop();
      return new Yices2Model(model, this, creator);
    } else {
      return new Yices2Model(curEnv.getModel(), this, creator);
    }
  }

  private List<BooleanFormula> encapsulate(int[] terms) {
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (int t : terms) {
      result.add(creator.encapsulateBoolean(t));
    }
    return result;
  }

  private int[] uncapsulate(Collection<BooleanFormula> terms) {
    int[] result = new int[terms.size()];
    int i = 0;
    for (BooleanFormula t : terms) {
      result[i++] = creator.extractInfo(t);
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    return encapsulate(curEnv.getUnsatCore());
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    checkGenerateUnsatCoresOverAssumptions();
    boolean sat = !isUnsatWithAssumptions(pAssumptions);
    return sat ? Optional.empty() : Optional.of(encapsulate(curEnv.getUnsatCore()));
  }

  @Override
  public void close() {
    if (!closed) {
      curEnv.close();
      stackSizeToUnsat = Integer.MAX_VALUE;
    }
    super.close();
  }
}
