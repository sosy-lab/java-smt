// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;
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
  }

  protected static SMTConfig getConfigInstance(
      int randomSeed, boolean interpolation, int algBool, int algUf, int algLra) {
    SMTConfig config = new SMTConfig();
    config.setRandomSeed(randomSeed);
    config.setInterpolation(interpolation);

    if (interpolation) {
      config.setOption(":interpolation-bool-algorithm", new SMTOption(algBool));
      config.setOption(":interpolation-euf-algorithm", new SMTOption(algUf));
      config.setOption(":interpolation-lra-algorithm", new SMTOption(algLra));
    }
    return config;
  }

  final MainSolver getOsmtSolver() {
    return osmtSolver;
  }

  @Override
  public void push() throws InterruptedException {
    Preconditions.checkState(!closed);
    setChanged();
    super.push();
    osmtSolver.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    setChanged();
    Preconditions.checkState(size() > 0, "Tried to pop from an empty solver stack");
    osmtSolver.pop();
    super.pop();
  }

  @Nullable
  protected abstract T addConstraintImpl(PTRef f) throws InterruptedException;

  @Override
  @Nullable
  public T addConstraint(BooleanFormula pF) throws InterruptedException {
    Preconditions.checkState(!closed);
    setChanged();
    super.addConstraint(pF);
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

  /** Make sure that the assertions only use features supported by the selected sublogic. */
  private void checkCompatability() throws SolverException {

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

    if (usesIntegers && usesReals) {
      throw new SolverException("OpenSMT does not support mixed integer-real arithmetics");
    }

    List<String> errors = new ArrayList<>();
    if (usesUFs && !creator.hasUFs()) {
      errors.add("uninterpreted functions");
    }
    if (usesIntegers && !creator.hasIntegers()) {
      errors.add("integers");
    }
    if (usesReals && !creator.hasReals()) {
      errors.add("reals");
    }
    if (usesArrays && !creator.hasArrays()) {
      errors.add("arrays");
    }

    if (!errors.isEmpty()) {
      throw new SolverException(
          "Assertions use features that are not supported by the selected logic " + errors);
    }
  }

  @Override
  @SuppressWarnings("try")
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkCompatability();

    closeAllEvaluators();
    changedSinceLastSatQuery = false;

    try (ShutdownHook listener = new ShutdownHook(shutdownNotifier, osmtSolver::stop)) {
      shutdownNotifier.shutdownIfNecessary();
      sstat r = osmtSolver.check();
      shutdownNotifier.shutdownIfNecessary();

      if (r.equals(sstat.Error())) {
        throw new SolverException("OpenSMT crashed while checking satisfiablity");
      }
      if (r.equals(sstat.Undef())) {
        throw new InterruptedException();
      }

      return r.equals(sstat.False());
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  @Override
  public void close() {
    if (!closed) {
      osmtSolver.delete();
    }
    super.close();
  }
}
