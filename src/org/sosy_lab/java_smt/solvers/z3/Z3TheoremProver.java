// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;
import java.util.Collection;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;

class Z3TheoremProver extends Z3AbstractProver implements ProverEnvironment {

  private final long z3solver;
  private final ShutdownRequestListener interruptListener;

  private @Nullable Z3UserPropagator propagator = null;

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(creator, pMgr, pOptions, pLogfile, pShutdownNotifier);
    z3solver = Native.mkSolver(z3context);
    Native.solverIncRef(z3context, z3solver);

    interruptListener = reason -> Native.solverInterrupt(z3context, z3solver);
    shutdownNotifier.register(interruptListener);

    long z3params = Native.mkParams(z3context);
    Native.paramsIncRef(z3context, z3params);
    for (Entry<String, Object> entry : pSolverOptions.entrySet()) {
      addParameter(z3params, entry.getKey(), entry.getValue());
    }
    Native.solverSetParams(z3context, z3solver, z3params);
    Native.paramsDecRef(z3context, z3params);
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    push0();
    try {
      Native.solverPush(z3context, z3solver);
    } catch (Z3Exception exception) {
      throw creator.handleZ3Exception(exception);
    }
  }

  @Override
  protected void popImpl() {
    Native.solverPop(z3context, z3solver, 1);
    pop0();
  }

  @Override
  protected void assertContraint(long constraint) {
    Native.solverAssert(z3context, z3solver, constraint);
  }

  @Override
  protected void assertContraintAndTrack(long constraint, long symbol) {
    Native.solverAssertAndTrack(z3context, z3solver, constraint, symbol);
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    logSolverStack();
    int result;
    try {
      result = Native.solverCheck(z3context, z3solver);
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    int result;
    try {
      result =
          Native.solverCheckAssumptions(
              z3context,
              z3solver,
              assumptions.size(),
              assumptions.stream().mapToLong(creator::extractInfo).toArray());
    } catch (Z3Exception e) {
      throw creator.handleZ3Exception(e);
    }
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  private void undefinedStatusToException(int solverStatus)
      throws SolverException, InterruptedException {
    if (solverStatus == Z3_lbool.Z3_L_UNDEF.toInt()) {
      creator.shutdownNotifier.shutdownIfNecessary();
      final String reason = Native.solverGetReasonUnknown(z3context, z3solver);
      switch (reason) {
        case "canceled": // see Z3: src/tactic/tactic.cpp
        case "interrupted": // see Z3: src/solver/check_sat_result.cpp
        case "interrupted from keyboard": // see Z3: src/solver/check_sat_result.cpp
          throw new InterruptedException(reason);
        default:
          throw new SolverException("Z3 returned 'unknown' status, reason: " + reason);
      }
    }
  }

  @Override
  protected long getUnsatCore0() {
    return Native.solverGetUnsatCore(z3context, z3solver);
  }

  @Override
  protected long getZ3Model() {
    return Native.solverGetModel(z3context, z3solver);
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(
        Native.solverGetNumScopes(z3context, z3solver) == super.size(),
        "prover-size %s does not match stack-size %s",
        Native.solverGetNumScopes(z3context, z3solver),
        super.size());
    return super.size();
  }

  @Override
  protected long getStatistics0() {
    return Native.solverGetStatistics(z3context, z3solver);
  }

  @Override
  public boolean registerUserPropagator(UserPropagator prop) {
    Preconditions.checkState(!closed);
    if (propagator != null) {
      propagator.close();
    }
    propagator = new Z3UserPropagator(z3context, z3solver, creator, mgr, prop);
    prop.initializeWithBackend(propagator);
    return true;
  }

  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.solverToString(z3context, z3solver);
  }

  @Override
  public void close() {
    if (!closed) {
      Preconditions.checkArgument(
          Native.solverGetNumScopes(z3context, z3solver) >= 0,
          "a negative number of scopes is not allowed");

      Native.solverReset(z3context, z3solver); // remove all assertions from the solver
      Native.solverDecRef(z3context, z3solver);
      if (propagator != null) {
        propagator.close();
        propagator = null;
      }
      shutdownNotifier.unregister(interruptListener);
    }
    super.close();
  }
}
