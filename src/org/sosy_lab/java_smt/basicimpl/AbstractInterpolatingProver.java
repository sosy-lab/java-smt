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

import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public abstract class AbstractInterpolatingProver<F> extends AbstractProverWithAllSat<F>
    implements InterpolatingProverEnvironment<F> {

  private final FormulaCreator<?, ?, ?, ?> creator;

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      FormulaCreator<?, ?, ?, ?> pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pBmgr, pShutdownNotifier);
    creator = pCreator;
  }
}
