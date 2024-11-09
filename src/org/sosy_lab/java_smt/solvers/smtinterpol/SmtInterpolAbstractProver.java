// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableMap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

@SuppressWarnings("ClassTypeParameterName")
abstract class SmtInterpolAbstractProver<T> extends AbstractProver<T> {

  protected final Script env;
  protected final FormulaCreator<Term, Sort, Script, FunctionSymbol> creator;
  protected final SmtInterpolFormulaManager mgr;
  protected final Deque<PersistentMap<String, BooleanFormula>> annotatedTerms = new ArrayDeque<>();
  protected final ShutdownNotifier shutdownNotifier;

  private static final String PREFIX = "term_"; // for termnames
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different termnames

  SmtInterpolAbstractProver(
      SmtInterpolFormulaManager pMgr,
      Script pEnv,
      Set<ProverOptions> options,
      ShutdownNotifier pShutdownNotifier) {
    super(options);
    mgr = pMgr;
    creator = pMgr.getFormulaCreator();
    env = pEnv;
    shutdownNotifier = pShutdownNotifier;
    annotatedTerms.add(PathCopyingPersistentTreeMap.of());
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  protected void pushImpl() {
    annotatedTerms.add(annotatedTerms.peek());
    env.push(1);
  }

  @Override
  protected void popImpl() {
    env.pop(1);
    annotatedTerms.pop();
  }

  @CanIgnoreReturnValue
  protected String addConstraint0(BooleanFormula constraint) {
    Preconditions.checkState(!closed);

    // create a term-name, used for unsat-core or interpolation, otherwise there is no overhead.
    String termName = generateTermName();
    Term t = mgr.extractInfo(constraint);
    Term annotatedTerm = env.annotate(t, new Annotation(":named", termName));
    annotatedTerms.push(annotatedTerms.pop().putAndCopy(termName, constraint));

    env.assertTerm(annotatedTerm);
    return termName;
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    checkState(!closed);

    // We actually terminate SmtInterpol during the analysis
    // by using a shutdown listener. However, SmtInterpol resets the
    // mStopEngine flag in DPLLEngine before starting to solve,
    // so we check here, too.
    shutdownNotifier.shutdownIfNecessary();

    LBool result = env.checkSat();
    switch (result) {
      case SAT:
        return false;
      case UNSAT:
        return true;
      case UNKNOWN:
        Object reason = env.getInfo(":reason-unknown");
        if (!(reason instanceof ReasonUnknown)) {
          throw new SMTLIBException("checkSat returned UNKNOWN with unknown reason " + reason);
        }
        switch ((ReasonUnknown) reason) {
          case MEMOUT:
            // SMTInterpol catches OOM, but we want to have it thrown.
            throw new OutOfMemoryError("Out of memory during SMTInterpol operation");
          case CANCELLED:
            shutdownNotifier.shutdownIfNecessary(); // expected if we requested termination
            throw new SMTLIBException("checkSat returned UNKNOWN with unexpected reason " + reason);
          default:
            throw new SMTLIBException("checkSat returned UNKNOWN with unexpected reason " + reason);
        }

      default:
        throw new SMTLIBException("checkSat returned " + result);
    }
  }

  @SuppressWarnings("resource")
  @Override
  public org.sosy_lab.java_smt.api.Model getModel() {
    checkState(!closed);
    checkGenerateModels();
    final Model model;
    try {
      model = env.getModel();
    } catch (SMTLIBException e) {
      if (e.getMessage().contains("Context is inconsistent")) {
        throw new IllegalStateException(BasicProverEnvironment.NO_MODEL_HELP, e);
      } else {
        // new stacktrace, but only the library calls are missing.
        throw e;
      }
    }
    return new CachingModel(
        new SmtInterpolModel(
            this,
            model,
            creator,
            transformedImmutableSetCopy(getAssertedFormulas(), mgr::extractInfo)));
  }

  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkState(!closed);
    checkGenerateUnsatCores();
    return getUnsatCore0(annotatedTerms.peek());
  }

  /**
   * small helper method, because we guarantee that {@link
   * ProverOptions#GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS} is independent of {@link
   * ProverOptions#GENERATE_UNSAT_CORE}.
   *
   * @param annotatedConstraints from where to extract the constraints for the unsat-core. Note that
   *     further constraints can also contribute to unsatisfiability.
   */
  private List<BooleanFormula> getUnsatCore0(Map<String, BooleanFormula> annotatedConstraints) {
    return FluentIterable.from(env.getUnsatCore())
        .transform(Term::toString)
        .filter(annotatedConstraints::containsKey) // filter for constraints under test.
        .transform(annotatedConstraints::get)
        .toList();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws InterruptedException, SolverException {
    checkState(!closed);
    checkGenerateUnsatCoresOverAssumptions();
    Map<String, BooleanFormula> annotatedConstraints = new LinkedHashMap<>();
    push();
    for (BooleanFormula assumption : assumptions) {
      String name = addConstraint0(assumption);
      annotatedConstraints.put(name, assumption);
    }
    Optional<List<BooleanFormula>> result =
        isUnsat() ? Optional.of(getUnsatCore0(annotatedConstraints)) : Optional.empty();
    pop();
    return result;
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
    SmtInterpolSolverContext.flatten(builder, "", env.getInfo(":all-statistics"));
    return builder.buildOrThrow();
  }

  @Override
  public void close() {
    if (!closed) {
      annotatedTerms.clear();
      env.pop(size());
    }
    super.close();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Assumption-solving is not supported.");
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    checkState(!closed);
    checkGenerateAllSat();

    Term[] importantTerms = new Term[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantTerms[i++] = mgr.extractInfo(impF);
    }
    // We actually terminate SmtInterpol during the analysis
    // by using a shutdown listener. However, SmtInterpol resets the
    // mStopEngine flag in DPLLEngine before starting to solve,
    // so we check here, too.
    shutdownNotifier.shutdownIfNecessary();
    for (Term[] model : env.checkAllsat(importantTerms)) {
      callback.apply(Collections3.transformedImmutableListCopy(model, creator::encapsulateBoolean));
    }
    return callback.getResult();
  }
}
