// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static org.sosy_lab.java_smt.solvers.opensmt.OpenSMTProof.generateProof;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext.OpenSMTOptions;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.MainSolver;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTConfig;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTOption;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.Symbol;
import org.sosy_lab.java_smt.solvers.opensmt.api.sstat;

public abstract class OpenSmtAbstractProver<T> extends AbstractProverWithAllSat<T> {

  protected final OpenSmtFormulaCreator creator;
  protected final MainSolver osmtSolver;
  protected final SMTConfig osmtConfig;
  private final FormulaManager formulaManager;

  private boolean changedSinceLastSatQuery = false;

  protected OpenSmtAbstractProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      SMTConfig pConfig,
      Set<ProverOptions> pOptions) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);

    creator = pFormulaCreator;

    // BUGFIX: We need to store the SMTConfig reference to make sure the underlying C++ object does
    // not get garbage collected
    osmtConfig = pConfig;
    osmtSolver = new MainSolver(creator.getEnv(), pConfig, "JavaSmt");
    formulaManager = pMgr; // needed for parsing formulas in proofs
  }

  protected static SMTConfig getConfigInstance(
      Set<ProverOptions> pOptions, OpenSMTOptions pSolverOptions, boolean interpolation) {
    SMTConfig config = new SMTConfig();
    config.setOption(":random-seed", new SMTOption(pSolverOptions.randomSeed));
    config.setOption(
        ":produce-models",
        new SMTOption(
            pOptions.contains(ProverOptions.GENERATE_MODELS)
                || pOptions.contains(ProverOptions.GENERATE_ALL_SAT)));
    SMTOption optUnsatCore = new SMTOption(pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE));
    config.setOption(":produce-unsat-cores", optUnsatCore);
    config.setOption(":print-cores-full", optUnsatCore);
    config.setOption(":produce-interpolants", new SMTOption(interpolation));
    config.setOption(
        ":produce-proofs", new SMTOption(pOptions.contains(ProverOptions.GENERATE_PROOFS)));
    if (interpolation) {
      config.setOption(":interpolation-bool-algorithm", new SMTOption(pSolverOptions.algBool));
      config.setOption(":interpolation-euf-algorithm", new SMTOption(pSolverOptions.algUf));
      config.setOption(":interpolation-lra-algorithm", new SMTOption(pSolverOptions.algLra));
    }
    return config;
  }

  final MainSolver getOsmtSolver() {
    return osmtSolver;
  }

  @Override
  protected void pushImpl() {
    setChanged();
    osmtSolver.push();
  }

  @Override
  protected void popImpl() {
    setChanged();
    osmtSolver.pop();
  }

  @Nullable
  protected abstract T addConstraintImpl(PTRef f) throws InterruptedException;

  @Override
  @Nullable
  protected T addConstraintImpl(BooleanFormula pF) throws InterruptedException {
    setChanged();
    PTRef f = creator.extractInfo(pF);
    return addConstraintImpl(f);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    checkGenerateModels();

    Model model =
        new OpenSmtModel(
            this, creator, Collections2.transform(getAssertedFormulas(), creator::extractInfo));
    return registerEvaluator(model);
  }

  @Override
  public Evaluator getEvaluator() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getEvaluatorWithoutChecks();
  }

  @SuppressWarnings("resource")
  @Override
  protected Evaluator getEvaluatorWithoutChecks() {
    return registerEvaluator(new OpenSmtEvaluator(this, creator));
  }

  protected void setChanged() {
    if (!changedSinceLastSatQuery) {
      changedSinceLastSatQuery = true;
      closeAllEvaluators();
    }
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    return super.getModelAssignments();
  }

  /**
   * Make sure that the assertions only use features supported by the selected logic. Otherwise,
   * OpenSMT will fail on checking satisfiability without further information, if the selected logic
   * is required for solving process.
   */
  private String getReasonFromSolverFeatures() {
    Logic osmtLogic = creator.getEnv();

    Map<String, PTRef> userDeclarations = new HashMap<>();
    for (PTRef asserted : Collections2.transform(getAssertedFormulas(), creator::extractInfo)) {
      userDeclarations.putAll(creator.extractVariablesAndUFs(asserted, true));
    }

    boolean usesUFs = false;
    boolean usesIntegers = false;
    boolean usesReals = false;
    boolean usesArrays = false;

    for (PTRef term : userDeclarations.values()) {
      SymRef ref = osmtLogic.getSymRef(term);
      Symbol sym = osmtLogic.getSym(ref);

      if (sym.size() > 1) {
        usesUFs = true;
      }

      SRef sort = sym.rsort();
      if (osmtLogic.isArraySort(sort)) {
        usesArrays = true;
      }
      if (sort.equals(creator.getIntegerType())) {
        usesIntegers = true;
      }
      if (sort.equals(creator.getRationalType())) {
        usesReals = true;
      }
    }

    return getReasonFromSolverFeatures(usesUFs, usesIntegers, usesReals, usesArrays);
  }

  protected String getReasonFromSolverFeatures(
      boolean usesUFs, boolean usesIntegers, boolean usesReals, boolean usesArrays) {
    if (usesIntegers && usesReals) {
      return "OpenSMT does not support mixed integer-real arithmetics.";
    }

    List<String> errors = new ArrayList<>();
    if (usesUFs && !creator.getLogic().doesLogicSupportUFs()) {
      errors.add("uninterpreted function");
    }
    if (usesIntegers && !creator.getLogic().doesLogicSupportIntegers()) {
      errors.add("integer");
    }
    if (usesReals && !creator.getLogic().doesLogicSupportReals()) {
      errors.add("real");
    }
    if (usesArrays && !creator.getLogic().doesLogicSupportArrays()) {
      errors.add("array");
    }

    if (errors.isEmpty()) {
      return "Unknown reason.";
    } else {
      return String.format(
          "Assertions use features %s that are not supported by the specified logic %s.",
          errors, creator.getLogic());
    }
  }

  @Override
  @SuppressWarnings("try") // ShutdownHook is never referenced, and this is correct.
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    closeAllEvaluators();
    changedSinceLastSatQuery = false;

    sstat result;
    try (ShutdownHook listener = new ShutdownHook(shutdownNotifier, osmtSolver::stop)) {
      shutdownNotifier.shutdownIfNecessary();
      try {
        result = osmtSolver.check();
      } catch (Exception e) {
        if (e.getMessage().isEmpty()) {
          // OpenSMT does not support all combinations of theories/logics and crashes on
          // unsupported formula instances. We try to provide hints for the crash.
          // Support for logics/features is checked lazily, i.e., only in case of an exception,
          // such that the solver can simplify and try to reason about a query as far as possible.
          // In several cases, the complex logics are not required for reasoning
          // and OpenSMT succeeds with solving a query.
          String reason = String.format(" Most likely reason: %s", getReasonFromSolverFeatures());
          throw new SolverException(
              String.format(
                  "OpenSMT crashed while checking satisfiability. Most likely reason: %s", reason));
        } else {
          throw new SolverException("OpenSMT crashed while checking satisfiability.", e);
        }
      }
      shutdownNotifier.shutdownIfNecessary();
    }

    if (result.equals(sstat.Error())) {
      throw new SolverException("OpenSMT crashed while checking satisfiability.");
    } else if (result.equals(sstat.Undef())) {
      throw new InterruptedException();
    } else {
      return result.equals(sstat.False());
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    Preconditions.checkState(!changedSinceLastSatQuery);
    return Lists.transform(osmtSolver.getUnsatCore(), creator::encapsulateBoolean);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support solving with assumptions.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support solving with assumptions.");
  }

  // TODO perform resolution throughout the DAG to calculate formulas that might not be present.
  @Override
  public Proof getProof() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(this.isUnsat());
    checkGenerateProofs();
    // throw new UnsupportedOperationException(
    //    "Proof generation is not available for the current solver.");

    // System.out.println(osmtSolver.printResolutionProofSMT2());
    OpenSMTProof root = generateProof(osmtSolver.printResolutionProofSMT2(), creator);
    parseFormulas(root);
    return root;
  }

  private void parseFormulas(Proof root) {
    Deque<Proof> stack = new ArrayDeque<>();
    stack.push(root);

    while (!stack.isEmpty()) {
      Proof proof = stack.pop();
      Formula formula;
      String formulaString = ((OpenSMTProof) proof).sFormula;
      // System.out.println(formulaString);

      if (formulaString != null) {
        try {
          // Replace integer literals with real literals to avoid parsing errors
          if (creator.getLogic().doesLogicSupportReals()) {
            // This fixes error where OpenSMT tries to parse Int and Real operations e.g. (* Int
            // Real) but when doing operations between integers it causes that exact problem.
            // formulaString = formulaString.replaceAll("(?<=[\\s\\(])(-?\\d+)(?=[\\s\\)])",
            // "$1.0");
          }

          if (formulaString.startsWith("(")) {
            formulaString = "(assert " + formulaString + ")";
            formula = formulaManager.parse(formulaString);
            // System.out.println(formula);
            ((OpenSMTProof) proof).setFormula(formula);
          } else if (formulaString.equals("-") || formulaString.equals("false")) {
            formula = formulaManager.getBooleanFormulaManager().makeFalse();
            ((OpenSMTProof) proof).setFormula(formula);
          } else {
            if (formulaManager.isValidName(formulaString)) {
              formula = formulaManager.getBooleanFormulaManager().makeVariable(formulaString);
              ((OpenSMTProof) proof).setFormula(formula);
            } else {
              formula = formulaManager.parse("(assert (" + formulaString + "))");
              ((OpenSMTProof) proof).setFormula(formula);
            }
          }
        } catch (IllegalArgumentException e) {
          throw new IllegalArgumentException("Error parsing formula: " + formulaString, e);
        }
      } else {
        ((OpenSMTProof) proof).setFormula(null);
      }

      // ((OpenSMTSubproof) subproof).setFormula(formula);
      // System.out.println(".");
      // System.out.println(subproof.getFormula());
      if (!proof.isLeaf()) {
        Proof[] children = proof.getChildren().toArray(new Proof[0]);
        for (int i = children.length - 1; i >= 0; i--) {
          stack.push(children[i]);
        }
      }
    }
  }

  @Override
  public void close() {
    if (!closed) {
      osmtSolver.delete();
    }
    super.close();
  }
}
