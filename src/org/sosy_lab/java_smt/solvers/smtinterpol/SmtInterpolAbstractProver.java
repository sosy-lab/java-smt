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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof.Subproof;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolProof.SmtInterpolProofNodeCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolProof.SmtInterpolProofNodeCreator.ProvitionalProofNode;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolProof.SmtInterpolSubproof;

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
  public Subproof getProof() throws InterruptedException {
    checkState(!closed);
    checkGenerateProofs();
    checkState(isUnsat());

    final Term tProof;
    try {
      tProof = env.getProof();
    } catch (SMTLIBException e) {
      if (e.getMessage().contains("Context is inconsistent")) {
        throw new IllegalStateException("Cannot get proof from satisfiable environment", e);
      } else {
        throw e;
      }
    }

    SmtInterpolProofNodeCreator pc =
        new SmtInterpolProofNodeCreator(
            (SmtInterpolFormulaCreator) this.creator, new SmtInterpolProof());
    ProvitionalProofNode ppn = pc.createPPNDag(tProof);
    Subproof proof = pc.createProof(ppn);
    // Before being able to perfom resolution, we need to calculate the formulas resulting from
    // applying the axioms, as it stands, just the input for the axiom is stored.
    // clausifyResChain(proof, mgr.getBooleanFormulaManager());

    return proof;
  }

  public Term smtInterpolGetProof(){
    Term tProof;
    try {
      tProof = env.getProof();
    } catch (SMTLIBException e) {
      if (e.getMessage().contains("Context is inconsistent")) {
        throw new IllegalStateException("Cannot get proof from satisfiable environment", e);
      } else {
        throw e;
      }
    }
    return tProof;
  }

  @Override
  public void close() {
    if (!closed) {
      annotatedTerms.clear();
      env.resetAssertions();
      env.exit();
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

  // update all RES_CHAIN nodes in the proof DAG by computing resolution
  // formulas and return the updated root node with formulas attached.
  @SuppressWarnings("unused")
  private void clausifyResChain(Subproof root, BooleanFormulaManager bfmgr) {
    Map<Subproof, Boolean> visited = new HashMap<>(); // Track visited nodes
    ArrayDeque<Subproof> stack = new ArrayDeque<>();

    stack.push(root); // Start with the root node
    visited.put(root, Boolean.FALSE); // Mark root as unvisited

    while (!stack.isEmpty()) {
      Subproof node = stack.peek(); // Look at the top node, but don't pop yet

      if (visited.get(node).equals(Boolean.FALSE)) {
        // First time visiting this node
        visited.put(node, Boolean.TRUE); // Mark node as visited

        // Push all children onto stack
        LinkedHashSet<Subproof> children = node.getArguments();
        List<Subproof> childrenList = new ArrayList<>(children);
        for (int i = childrenList.size() - 1; i >= 0; i--) {
          Subproof child = childrenList.get(i);
          if (!visited.containsKey(child)) {
            stack.push(child); // Only push unvisited children
            visited.put(child, Boolean.FALSE); // Mark child as unvisited
          }
        }
      } else {
        // All children have been visited, now process the node
        stack.pop(); // Pop the current node as we are done processing its children

        // Check if this node is a RES_CHAIN, process if true
        if (node.getRule().equals(ResAxiom.RESOLUTION)) {
          processResChain(node, bfmgr); // Process RES_CHAIN node
        }
      }
    }
  }

  // process proof nodes and compute formulas for res-chain nodes
  private void processResChain(Subproof node, BooleanFormulaManager bfmgr) {
    LinkedHashSet<Subproof> childrenSet = node.getArguments();
    List<Subproof> children = new ArrayList<>(childrenSet);

    // If the current node is a RES_CHAIN, compute the resolved formula
    if (node.getRule().equals(ResAxiom.RESOLUTION)) {
      // Sanity check: res-chain nodes must have an odd number of children (clause, pivot, clause,
      // ..., clause)
      if (children.size() < 3 || children.size() % 2 == 0) {
        throw new IllegalArgumentException("Invalid res-chain structure: must be odd and >= 3");
      }

      // Begin resolution chain: start with the first clause
      BooleanFormula current = (BooleanFormula) children.get(0).getFormula();

      // Apply resolution iteratively using pivot, clause pairs
      for (int i = 1; i < children.size() - 1; i += 2) {
        BooleanFormula pivot = (BooleanFormula) children.get(i).getFormula();
        BooleanFormula nextClause = (BooleanFormula) children.get(i + 1).getFormula();
        current = resolve(current, nextClause, pivot, bfmgr); // Perform resolution step
      }

      // Store the resolved formula in the current node
      ((SmtInterpolSubproof) node).setFormula(current);
    }
  }

  // Perform resolution between two  clauses using a given pivot
  private BooleanFormula resolve(
      BooleanFormula clause1,
      BooleanFormula clause2,
      BooleanFormula pivot,
      BooleanFormulaManager bfmgr) {
    List<BooleanFormula> literals1 = flattenLiterals(clause1, bfmgr);
    List<BooleanFormula> literals2 = flattenLiterals(clause2, bfmgr);
    List<BooleanFormula> combined = new ArrayList<>();

    for (BooleanFormula lit : literals1) {
      if (!isComplement(lit, pivot, bfmgr)) {
        combined.add(lit);
      }
    }

    List<BooleanFormula> temp = new ArrayList<>();

    for (BooleanFormula lit : literals2) {
      if (!isComplement(lit, pivot, bfmgr)) {
        temp.add(lit);
      }
    }

    combined.addAll(temp);

    if (combined.isEmpty()) {
      return bfmgr.makeFalse();
    } else if (combined.size() == 1) {
      return combined.get(0);
    } else {
      return bfmgr.or(combined);
    }
  }

  // Helper method to flatten an OR/AND-formula into a list of disjunctive literals
  private List<BooleanFormula> flattenLiterals(
      BooleanFormula formula, BooleanFormulaManager bfmgr) {
    List<BooleanFormula> result = new ArrayList<>();

    bfmgr.visit(
        formula,
        new BooleanFormulaVisitor<>() {
          @Override
          public TraversalProcess visitOr(List<BooleanFormula> operands) {
            for (BooleanFormula op : operands) {
              result.addAll(flattenLiterals(op, bfmgr));
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAnd(List<BooleanFormula> operands) {
            for (BooleanFormula op : operands) {
              result.addAll(flattenLiterals(op, bfmgr));
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            result.add(formula); // add original NOT node
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
            result.add(formula); // add original atom
            return TraversalProcess.SKIP;
          }

          // others unchanged...
          @Override
          public TraversalProcess visitXor(BooleanFormula one, BooleanFormula two) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitEquivalence(BooleanFormula one, BooleanFormula two) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitImplication(BooleanFormula one, BooleanFormula two) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula c, BooleanFormula t, BooleanFormula e) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier q, BooleanFormula qBody, List<Formula> vars, BooleanFormula body) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitConstant(boolean value) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitBoundVar(BooleanFormula var, int index) {
            return TraversalProcess.SKIP;
          }
        });

    return result;
  }

  // Check whether two formulas are logical complements
  private boolean isComplement(BooleanFormula a, BooleanFormula b, BooleanFormulaManager bfmgr) {
    // Define the visitor to check for complement relation
    final boolean[] isComplement = {false};

    bfmgr.visitRecursively(
        a,
        new BooleanFormulaVisitor<>() {
          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            // Check if the negation of 'operand' equals 'b'
            if (operand.equals(b)) {
              isComplement[0] = true;
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
            if (atom.equals(b)) {
              isComplement[0] = true;
            }
            return TraversalProcess.SKIP;
          }

          // Default implementation for other nodes, such as OR, AND, etc.
          @Override
          public TraversalProcess visitOr(List<BooleanFormula> operands) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAnd(List<BooleanFormula> operands) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitXor(BooleanFormula var1, BooleanFormula var2) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitEquivalence(BooleanFormula var1, BooleanFormula var2) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitImplication(BooleanFormula var1, BooleanFormula var2) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula c, BooleanFormula t, BooleanFormula e) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier q, BooleanFormula qBody, List<Formula> vars, BooleanFormula body) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitConstant(boolean value) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitBoundVar(BooleanFormula var, int index) {
            return TraversalProcess.SKIP;
          }
        });

    return isComplement[0];
  }
}
