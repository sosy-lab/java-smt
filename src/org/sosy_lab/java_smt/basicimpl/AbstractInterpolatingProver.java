/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolatingProver<TFormulaInfo, TType>
        extends AbstractProverWithAllSat<TFormulaInfo>
        implements InterpolatingProverEnvironment<TFormulaInfo> {

  private final FormulaCreator<TFormulaInfo, TType, ?, ?> creator;
  private final FormulaManager mgr;
  private final QuantifiedFormulaManager qfmgr;
  private final BooleanFormulaManager bmgr;

  protected AbstractInterpolatingProver(
          Set<ProverOptions> pOptions,
          FormulaManager pMgr,
          BooleanFormulaManager pBmgr,
          QuantifiedFormulaManager pQfmgr,
          ShutdownNotifier pShutdownNotifier,
          FormulaCreator<?, ?, ?, ?> pCreator) {
    super(pOptions, pMgr, pBmgr, pQfmgr, pShutdownNotifier);
    mgr = pMgr;
    bmgr = pBmgr;
    creator = (FormulaCreator<TFormulaInfo, TType, ?, ?>) pCreator;
    qfmgr = pQfmgr;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
          throws SolverException, InterruptedException {
    return getModelBasedInterpolant(pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
          List<? extends Collection<TFormulaInfo>> partitionedFormulas,
          int[] startOfSubTree) throws SolverException, InterruptedException {
    return List.of();
  }

  private BooleanFormula getModelBasedInterpolant(Collection<TFormulaInfo> pFormulasOfA) {
    checkState(!closed);
    checkArgument(getAssertedConstraintIds().containsAll(pFormulasOfA),
            "interpolation can only be done over previously asserted formulas.");

    return null;
  }
}
