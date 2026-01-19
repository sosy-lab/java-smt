// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.solvers.cvc5.CVC5Proof.generateProofImpl;

import com.google.common.collect.Collections2;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.CVC5ApiRecoverableException;
import io.github.cvc5.Kind;
import io.github.cvc5.Result;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.UnknownExplanation;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;

abstract class CVC5AbstractProver<T> extends AbstractProverWithAllSat<T> {

  private static final UniqueIdGenerator ID_GENERATOR = new UniqueIdGenerator();

  protected final CVC5FormulaCreator creator;
  private final int randomSeed;
  private final ImmutableMap<String, String> furtherOptionsMap;
  protected Solver solver; // final in incremental mode, non-final in non-incremental mode
  protected final Deque<PersistentMap<String, Term>> assertedTerms = new ArrayDeque<>();

  // TODO: does CVC5 support separation logic in incremental mode?
  //  --> No. In incremental mode, CVC5 aborts when calling addConstraint(...).
  //  This means, we have to use non-incremental mode when SL is enabled.
  //  This also means, that push/pop are not supported when SL is enabled and we implement
  //  our own stack for asserted terms, and use a different solver instance for each sat check.
  protected final boolean incremental;

  protected CVC5AbstractProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed,
      ImmutableSet<ProverOptions> pOptions,
      FormulaManager pMgr,
      ImmutableMap<String, String> pFurtherOptionsMap) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);

    creator = pFormulaCreator;
    furtherOptionsMap = pFurtherOptionsMap;
    randomSeed = pRandomSeed;
    incremental = !enableSL;
    assertedTerms.add(PathCopyingPersistentTreeMap.of());

    if (incremental) {
      solver = getNewSolver();
    }
  }

  protected Solver getNewSolver() {
    Solver newSolver = new Solver(creator.getEnv());
    try {
      CVC5SolverContext.setSolverOptions(newSolver, randomSeed, furtherOptionsMap);
    } catch (CVC5ApiRecoverableException e) {
      // We've already used these options in CVC5SolverContext, so there should be no exception
      throw new AssertionError("Unexpected exception", e);
    }

    newSolver.setOption("incremental", incremental ? "true" : "false");
    newSolver.setOption("produce-models", generateModels ? "true" : "false");
    newSolver.setOption("produce-unsat-cores", generateUnsatCores ? "true" : "false");

    newSolver.setOption("produce-assertions", "true");
    newSolver.setOption("dump-models", "true");
    newSolver.setOption("produce-proofs", generateProofs ? "true" : "false");

    // Set Strings option to enable all String features (such as lessOrEquals)
    newSolver.setOption("strings-exp", "true");

    // Enable experimental array features
    // Needed when array constants (= with default element) are used
    newSolver.setOption("arrays-exp", "true");

    // Enable more complete quantifier solving (for more info see CVC5QuantifiedFormulaManager)
    newSolver.setOption("full-saturate-quant", "true");

    // if no logic is set in CVC5, select the broadest logic available: "ALL"
    if (!newSolver.isLogicSet()) {
      try {
        newSolver.setLogic("ALL");
      } catch (CVC5ApiException e) {
        throw new AssertionError("Unexpected exception", e);
      }
    }

    return newSolver;
  }

  @Override
  protected boolean hasPersistentModel() {
    return false;
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    assertedTerms.push(assertedTerms.peek()); // add copy of top-level
    if (incremental) {
      try {
        solver.push();
      } catch (CVC5ApiException e) {
        throw new IllegalStateException(
            "You tried to use push() on an CVC5 assertion stack illegally.", e);
      }
    }
  }

  @Override
  protected void popImpl() {
    if (incremental) {
      try {
        solver.pop();
      } catch (CVC5ApiException e) {
        throw new IllegalStateException(
            "You tried to use pop() on an CVC5 assertion stack illegally.", e);
      }
    }
    assertedTerms.pop();
  }

  @CanIgnoreReturnValue
  protected String addConstraint0(BooleanFormula pF) {
    checkState(!closed);
    Term exp = creator.extractInfo(pF);
    if (incremental) {
      solver.assertFormula(exp);
    }
    String id = "ID_" + ID_GENERATOR.getFreshId();
    assertedTerms.push(assertedTerms.pop().putAndCopy(id, exp));
    return id;
  }

  @SuppressWarnings("resource")
  @Override
  public CVC5Model getModel() throws SolverException {
    checkGenerateModels();
    // special case for CVC5: Models are not permanent and need to be closed
    // before any change is applied to the prover stack. So, we register the Model as Evaluator.
    return registerEvaluator(
        new CVC5Model(
            this, creator, Collections2.transform(getAssertedFormulas(), creator::extractInfo)));
  }

  @Override
  public Evaluator getEvaluator() {
    checkGenerateModels();
    return getEvaluatorWithoutChecks();
  }

  @SuppressWarnings("resource")
  @Override
  protected Evaluator getEvaluatorWithoutChecks() {
    return registerEvaluator(new CVC5Evaluator(this, creator));
  }

  @Override
  @SuppressWarnings("try")
  protected boolean isUnsatImpl() throws InterruptedException, SolverException {
    closeAllEvaluators();
    if (!incremental) {
      // in non-incremental mode, we need to create a new solver instance for each sat check
      if (solver != null) {
        solver.deletePointer(); // cleanup
      }
      solver = getNewSolver();

      ImmutableSet<BooleanFormula> assertedFormulas = getAssertedFormulas();
      if (enableSL) {
        declareHeap(assertedFormulas);
      }
      assertedFormulas.forEach(f -> solver.assertFormula(creator.extractInfo(f)));
    }

    Result result;
    try {
      result = solver.checkSat();
    } catch (Exception e) {
      // we actually only want to catch CVC5ApiException, but need to catch all.
      throw new SolverException("CVC5 failed during satisfiability check", e);
    } finally {
      /* Shutdown currently not possible in CVC5. */
      shutdownNotifier.shutdownIfNecessary();
    }
    return convertSatResult(result);
  }

  private void declareHeap(ImmutableSet<BooleanFormula> pAssertedFormulas) throws SolverException {
    // get heap sort from asserted terms
    final Multimap<Sort, Sort> heapSorts;
    try {
      heapSorts = getHeapSorts(pAssertedFormulas);
    } catch (CVC5ApiException e) {
      throw new SolverException("CVC5 failed during heap sort collection", e);
    }

    // if there are no heaps, skip the rest
    if (heapSorts.isEmpty()) {
      return;
    }

    // if there are multiple heaps with different sorts, we cannot handle this
    if (heapSorts.size() > 1) {
      throw new SolverException(
          "CVC5 SL support is limited to one heap with one sort. Found heaps with sorts: "
              + heapSorts);
    }

    // get the (only) heap sort, and declare it in the solver, once before the first sat check
    final Sort heapSort = checkNotNull(Iterables.getOnlyElement(heapSorts.keySet()));
    final Sort elementSort = checkNotNull(Iterables.getOnlyElement(heapSorts.get(heapSort)));
    solver.declareSepHeap(heapSort, elementSort);
  }

  private Multimap<Sort, Sort> getHeapSorts(ImmutableSet<BooleanFormula> pAssertedFormulas)
      throws CVC5ApiException {
    final Deque<Term> waitlist = new ArrayDeque<>();
    for (BooleanFormula f : pAssertedFormulas) {
      waitlist.add(creator.extractInfo(f));
    }

    // traverse all subterms of assertedFormulas and collect heap sorts
    final Multimap<Sort, Sort> heapSorts = HashMultimap.create();
    boolean requiresHeapSort = false;
    final Set<Term> finished = new HashSet<>();
    while (!waitlist.isEmpty()) {
      final Term current = waitlist.pop();
      if (finished.add(current)) {
        // If current is a SEP_PTO, collect the heap sort from its children,
        // we ignore all other SL terms (like SEP_EMP, SEP_STAR, SEP_WAND).
        // SEP_EMP would be interesting, but does not provide the heap sort and element sort.
        if (current.getKind() == Kind.SEP_PTO) {
          heapSorts.put(current.getChild(0).getSort(), current.getChild(1).getSort());
        } else if (current.getKind() == Kind.SEP_EMP) {
          // SEP_EMP is sortless, but we need to declare the heap sort in CVC5.
          requiresHeapSort = true;
        }
        // add all children to the waitlist
        for (int i = 0; i < current.getNumChildren(); i++) {
          waitlist.push(current.getChild(i));
        }
      }
    }

    // if we found SEP_EMP but no SEP_PTO, we still need a heap sort
    if (requiresHeapSort && heapSorts.isEmpty()) {
      // use Integer->Integer as default heap sort
      heapSorts.put(creator.getIntegerType(), creator.getIntegerType());
    }

    return heapSorts;
  }

  private boolean convertSatResult(Result result) throws InterruptedException, SolverException {
    if (result.isUnknown()) {
      if (result.getUnknownExplanation().equals(UnknownExplanation.INTERRUPTED)) {
        throw new InterruptedException();
      } else {
        throw new SolverException(
            "CVC5 returned null or unknown on sat check. Exact result: " + result + ".");
      }
    }
    return result.isUnsat();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    List<BooleanFormula> converted = new ArrayList<>();
    for (Term aCore : solver.getUnsatCore()) {
      converted.add(creator.encapsulateBoolean(aCore));
    }
    return converted;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(ASSUMPTION_SOLVING_NOT_SUPPORTED);
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(ASSUMPTION_SOLVING_NOT_SUPPORTED);
  }

  @Override
  public Proof getProof() throws SolverException, InterruptedException {
    checkGenerateProofs();
    checkState(!closed);
    checkState(isUnsat());

    io.github.cvc5.Proof[] proofs = solver.getProof();
    checkState(proofs != null && proofs.length != 0, "No proof available");

    // CVC5ProofProcessor pp = new CVC5ProofProcessor(creator);
    try {
      return generateProofImpl(proofs[0], creator);
    } catch (CVC5ApiException e) {
      throw new SolverException("There was a problem generating proof", e);
    }
  }

  @Override
  public void close() {
    if (!closed) {
      assertedTerms.clear();
      solver.deletePointer();
    }
    super.close();
  }
}
