/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.google.common.collect.ImmutableMap;
import com.microsoft.z3legacy.Native;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class Z3LegacyTheoremProver extends Z3LegacyAbstractProver<Void> implements ProverEnvironment {

  Z3LegacyTheoremProver(
      Z3LegacyFormulaCreator creator,
      Z3LegacyFormulaManager pMgr,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(creator, pMgr, pOptions, pLogfile, pShutdownNotifier);
    long z3params = Native.mkParams(z3context);
    Native.paramsIncRef(z3context, z3params);
    for (Entry<String, Object> entry : pSolverOptions.entrySet()) {
      addParameter(z3params, entry.getKey(), entry.getValue());
    }
    Native.solverSetParams(z3context, z3solver, z3params);
    Native.paramsDecRef(z3context, z3params);
  }
}
