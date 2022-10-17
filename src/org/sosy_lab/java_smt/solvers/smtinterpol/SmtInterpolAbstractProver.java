// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableMap;
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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

@SuppressWarnings("ClassTypeParameterName")
abstract class SmtInterpolAbstractProver<T, AF> extends AbstractProver<T> {

  protected boolean closed = false;
  protected final Script env;
  protected final FormulaCreator<Term, Sort, Script, FunctionSymbol> creator;
  protected final SmtInterpolFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>();
  protected final Map<String, Term> annotatedTerms = new HashMap<>(); // Collection of termNames
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
    assertedFormulas.push(new ArrayList<>());
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public int size() {
    checkState(!closed);
    return assertedFormulas.size() - 1;
  }

  @Override
  public void push() {
    checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    env.push(1);
  }

  @Override
  public void pop() {
    checkState(!closed);
    assertedFormulas.pop();
    env.pop(1);
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

  protected abstract Collection<Term> getAssertedTerms();

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
    return new CachingModel(new SmtInterpolModel(this, model, creator, getAssertedTerms()));
  }

  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkState(!closed);
    checkGenerateUnsatCores();
    return getUnsatCore0();
  }

  /**
   * small helper method, because we guarantee that {@link
   * ProverOptions#GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS} is independent of {@link
   * ProverOptions#GENERATE_UNSAT_CORE}.
   */
  private List<BooleanFormula> getUnsatCore0() {
    return Collections3.transformedImmutableListCopy(
        env.getUnsatCore(),
        input -> creator.encapsulateBoolean(annotatedTerms.get(input.toString())));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws InterruptedException {
    checkState(!closed);
    checkGenerateUnsatCoresOverAssumptions();
    push();
    checkState(
        annotatedTerms.isEmpty(),
        "Empty environment required for UNSAT core over assumptions: %s",
        annotatedTerms);
    for (BooleanFormula assumption : assumptions) {
      String termName = generateTermName();
      Term t = mgr.extractInfo(assumption);
      Term annotated = env.annotate(t, new Annotation(":named", termName));
      annotatedTerms.put(termName, t);
      env.assertTerm(annotated);
    }
    Optional<List<BooleanFormula>> result =
        isUnsat() ? Optional.of(getUnsatCore0()) : Optional.empty();
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
      assertedFormulas.clear();
      annotatedTerms.clear();
      env.pop(assertedFormulas.size());
      closed = true;
    }
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
