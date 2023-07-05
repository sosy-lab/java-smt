// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import opensmt.VectorInt;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class OpenSmtInterpolatingProver extends OpenSmtAbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  OpenSmtInterpolatingProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      int pRandom,
      Set<ProverOptions> pOptions) {

    super(pFormulaCreator, pMgr, pShutdownNotifier, getConfigInstance(pRandom, true), pOptions);
  }

  @Override
  @Nullable
  protected Integer getConstraintName(BooleanFormula pF) {
    return getAssertedExpressions().size();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA) {
    Preconditions.checkState(!closed);
    return creator.encapsulateBoolean(
        osmtSolver.getInterpolationContext().getSingleInterpolant(new VectorInt(formulasOfA)));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas) {
    // FIXME: Add support for interpolation sequences
    throw new UnsupportedOperationException();
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException("OpenSMT does not support tree interpolants");
  }
}
