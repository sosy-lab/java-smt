// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.collect.ImmutableMap;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class Z3TheoremProver extends Z3AbstractProver<Void> implements ProverEnvironment {

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(creator, pMgr, pOptions, pSolverOptions, pLogfile, pShutdownNotifier);
  }

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      final long pZ3solver,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(creator, pMgr, pZ3solver, pOptions, pSolverOptions, pLogfile, pShutdownNotifier);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula f) throws InterruptedException {
    super.addConstraint0(f);
    return null;
  }
}
