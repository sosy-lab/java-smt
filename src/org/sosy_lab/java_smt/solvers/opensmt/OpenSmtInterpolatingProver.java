// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext.OpenSMTOptions;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorInt;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorVectorInt;

class OpenSmtInterpolatingProver extends OpenSmtAbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  // OpenSMT internally tracks all asserted formulas in one array and identifies them by index.
  // The index starts with 1.
  // We track the number of tracked formulas per level as reference point.
  private final Deque<Integer> trackedConstraints = new ArrayDeque<>();

  OpenSmtInterpolatingProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      OpenSMTOptions pSolverOptions) {
    super(
        pFormulaCreator,
        pMgr,
        pShutdownNotifier,
        getConfigInstance(pSolverOptions, true),
        pOptions);
    trackedConstraints.push(0); // initialize first level
  }

  @Override
  public Integer addConstraintImpl(PTRef f) throws InterruptedException {
    osmtSolver.insertFormula(f);
    Integer newId = trackedConstraints.pop() + 1;
    trackedConstraints.push(newId);
    return newId;
  }

  @Override
  public void push() throws InterruptedException {
    super.push();
    trackedConstraints.push(trackedConstraints.peek());
  }

  @Override
  public void pop() {
    trackedConstraints.pop();
    super.pop();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA) {
    checkState(!closed);
    return creator.encapsulateBoolean(
        osmtSolver.getInterpolationContext().getSingleInterpolant(new VectorInt(formulasOfA)));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas) {
    checkState(!closed);
    checkArgument(!partitionedFormulas.isEmpty(), "Interpolation sequence must not be empty");

    VectorVectorInt partitions = new VectorVectorInt();
    for (int i = 1; i < partitionedFormulas.size(); i++) {
      VectorInt prefix = new VectorInt();
      for (Collection<Integer> key : partitionedFormulas.subList(0, i)) {
        prefix.addAll(key);
      }
      partitions.add(prefix);
    }

    VectorPTRef itps = osmtSolver.getInterpolationContext().getPathInterpolants(partitions);

    List<BooleanFormula> result = new ArrayList<>();
    for (PTRef itp : itps) {
      result.add(creator.encapsulateBoolean(itp));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException("OpenSMT does not support tree interpolants");
  }
}
