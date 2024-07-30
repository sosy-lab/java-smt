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

import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolatingProver<F> extends AbstractProverWithAllSat<F>
    implements InterpolatingProverEnvironment<F> {

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pBmgr, pShutdownNotifier);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<F> formulasOfA)
      throws SolverException, InterruptedException {
    return null;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<F>> partitionedFormulas,
      int[] startOfSubTree) throws SolverException, InterruptedException {
    return List.of();
  }
}
