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
import com.microsoft.z3.Native.IntPtr;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;
import java.util.Collection;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class Z3OptimizationProver extends Z3AbstractProver implements OptimizationProverEnvironment {

  private final LogManager logger;
  private final long z3optSolver;

  @SuppressWarnings("checkstyle:parameternumber")
  Z3OptimizationProver(
      Z3FormulaCreator creator,
      LogManager pLogger,
      Z3FormulaManager pMgr,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, Object> pSolverOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pContextShutdownNotifier,
      @Nullable ShutdownNotifier pProverShutdownNotifier) {
    super(creator, pMgr, pOptions, pLogfile, pContextShutdownNotifier, pProverShutdownNotifier);
    z3optSolver = Native.mkOptimize(z3context);
    Native.optimizeIncRef(z3context, z3optSolver);
    logger = pLogger;

    // set parameters for the optimization solver
    long params = Native.mkParams(z3context);
    Native.paramsIncRef(z3context, params);
    for (Entry<String, Object> entry : pSolverOptions.entrySet()) {
      addParameter(params, entry.getKey(), entry.getValue());
    }
    Native.optimizeSetParams(z3context, z3optSolver, params);
    Native.paramsDecRef(z3context, params);
  }

  @Override
  public int maximize(Formula objective) {
    Preconditions.checkState(!closed);
    return Native.optimizeMaximize(z3context, z3optSolver, creator.extractInfo(objective));
  }

  @Override
  public int minimize(Formula objective) {
    Preconditions.checkState(!closed);
    return Native.optimizeMinimize(z3context, z3optSolver, creator.extractInfo(objective));
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    int status;
    wasLastSatCheckSat = false;
    try {
      status =
          Native.optimizeCheck(
              z3context,
              z3optSolver,
              0, // number of assumptions
              null // assumptions
              );
      stackChangedSinceLastQuery = false;
    } catch (Z3Exception ex) {
      throw creator.handleZ3Exception(ex, proverShutdownNotifier);
    }
    if (status == Z3_lbool.Z3_L_FALSE.toInt()) {
      return OptStatus.UNSAT;
    } else if (status == Z3_lbool.Z3_L_UNDEF.toInt()) {
      shutdownIfNecessary();
      logger.log(
          Level.INFO,
          "Solver returned an unknown status, explanation: ",
          Native.optimizeGetReasonUnknown(z3context, z3optSolver));
      return OptStatus.UNDEF;
    } else {
      wasLastSatCheckSat = true;
      return OptStatus.OPT;
    }
  }

  @Override
  protected void pushImpl() {
    push0();
    try {
      Native.optimizePush(z3context, z3optSolver);
    } catch (Z3Exception exception) {
      throw creator.handleZ3ExceptionAsRuntimeException(exception, proverShutdownNotifier);
    }
  }

  @Override
  protected void popImpl() {
    Native.optimizePop(z3context, z3optSolver);
    pop0();
  }

  @Override
  protected void assertContraint(long constraint) {
    Native.optimizeAssert(z3context, z3optSolver, constraint);
  }

  @Override
  protected void assertContraintAndTrack(long constraint, long symbol) {
    Native.optimizeAssertAndTrack(z3context, z3optSolver, constraint, symbol);
  }

  @Override
  protected long getUnsatCore0() {
    return Native.optimizeGetUnsatCore(z3context, z3optSolver);
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    logSolverStack();
    return check() == OptStatus.UNSAT;
  }

  @Override
  protected boolean isUnsatWithAssumptionsImpl(Collection<BooleanFormula> assumptions) {
    return false;
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    return round(handle, epsilon, Native::optimizeGetUpperAsVector);
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    return round(handle, epsilon, Native::optimizeGetLowerAsVector);
  }

  private interface RoundingFunction {
    long round(long context, long optContext, int handle);
  }

  private Optional<Rational> round(int handle, Rational epsilon, RoundingFunction direction) {
    Preconditions.checkState(!closed);

    // Z3 exposes the rounding result as a tuple (infinity, number, epsilon)
    long vector = direction.round(z3context, z3optSolver, handle);
    Native.astVectorIncRef(z3context, vector);
    assert Native.astVectorSize(z3context, vector) == 3;

    long inf = Native.astVectorGet(z3context, vector, 0);
    Native.incRef(z3context, inf);
    long value = Native.astVectorGet(z3context, vector, 1);
    Native.incRef(z3context, value);
    long eps = Native.astVectorGet(z3context, vector, 2);
    Native.incRef(z3context, eps);

    IntPtr ptr = new Native.IntPtr();
    boolean status = Native.getNumeralInt(z3context, inf, ptr);
    assert status;
    if (ptr.value != 0) {

      // Infinity.
      return Optional.empty();
    }

    Rational v = Rational.ofString(Native.getNumeralString(z3context, value));

    status = Native.getNumeralInt(z3context, eps, ptr);
    assert status;
    try {
      return Optional.of(v.plus(epsilon.times(Rational.of(ptr.value))));
    } finally {
      Native.astVectorDecRef(z3context, vector);
      Native.decRef(z3context, inf);
      Native.decRef(z3context, value);
      Native.decRef(z3context, eps);
    }
  }

  @Override
  protected long getZ3Model() {
    try {
      return Native.optimizeGetModel(z3context, z3optSolver);
    } catch (Z3Exception e) {
      throw creator.handleZ3ExceptionAsRuntimeException(e, proverShutdownNotifier);
    }
  }

  @Override
  protected long getStatistics0() {
    return Native.optimizeGetStatistics(z3context, z3optSolver);
  }

  /** Dumps the optimized objectives and the constraints on the solver in the SMT-lib format. */
  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.optimizeToString(z3context, z3optSolver);
  }

  @Override
  public void close() {
    if (!closed) {
      Native.optimizeDecRef(z3context, z3optSolver);
    }
    super.close();
  }
}
