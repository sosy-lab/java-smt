// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
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

  @Override
  public void push() throws InterruptedException {
    Preconditions.checkState(!closed);
    push0();
    try {
      Native.solverPush(z3context, z3solver);
    } catch (Z3Exception exception) {
      throw creator.handleZ3Exception(exception);
    }
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Native.solverPop(z3context, z3solver, 1);
    pop0();
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula f) throws InterruptedException {
    super.addConstraint0(f);
    return null;
  }
}
