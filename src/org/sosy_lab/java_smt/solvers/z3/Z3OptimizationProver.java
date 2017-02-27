/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.microsoft.z3.Native;
import com.microsoft.z3.Native.IntPtr;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;
import java.util.Optional;
import java.util.logging.Level;
import javax.annotation.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

class Z3OptimizationProver extends Z3AbstractProver<Void> implements OptimizationProverEnvironment {

  private final LogManager logger;
  private final long z3optContext;

  Z3OptimizationProver(Z3FormulaCreator creator, LogManager pLogger) {
    super(creator);
    z3optContext = Native.mkOptimize(z3context);
    Native.optimizeIncRef(z3context, z3optContext);
    logger = pLogger;
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    long z3Constraint = creator.extractInfo(constraint);
    Native.optimizeAssert(z3context, z3optContext, z3Constraint);
    return null;
  }

  @Override
  public int maximize(Formula objective) {
    Preconditions.checkState(!closed);
    Z3Formula z3Objective = (Z3Formula) objective;
    return Native.optimizeMaximize(z3context, z3optContext, z3Objective.getFormulaInfo());
  }

  @Override
  public int minimize(Formula objective) {
    Preconditions.checkState(!closed);
    Z3Formula z3Objective = (Z3Formula) objective;
    return Native.optimizeMinimize(z3context, z3optContext, z3Objective.getFormulaInfo());
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    int status;
    try {
      status = Native.optimizeCheck(z3context, z3optContext);
    } catch (Z3Exception ex) {
      throw creator.handleZ3Exception(ex);
    }
    if (status == Z3_lbool.Z3_L_FALSE.toInt()) {
      return OptStatus.UNSAT;
    } else if (status == Z3_lbool.Z3_L_UNDEF.toInt()) {
      creator.shutdownNotifier.shutdownIfNecessary();
      logger.log(
          Level.INFO,
          "Solver returned an unknown status, explanation: ",
          Native.optimizeGetReasonUnknown(z3context, z3optContext));
      return OptStatus.UNDEF;
    } else {
      return OptStatus.OPT;
    }
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    Native.optimizePush(z3context, z3optContext);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Native.optimizePop(z3context, z3optContext);
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    return check() == OptStatus.UNSAT;
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
    long vector = direction.round(z3context, z3optContext, handle);
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
    return Native.optimizeGetModel(z3context, z3optContext);
  }

  void setParam(String key, String value) {
    long keySymbol = Native.mkStringSymbol(z3context, key);
    long valueSymbol = Native.mkStringSymbol(z3context, value);
    long params = Native.mkParams(z3context);
    Native.paramsSetSymbol(z3context, params, keySymbol, valueSymbol);
    Native.optimizeSetParams(z3context, z3optContext, params);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    Native.optimizeDecRef(z3context, z3optContext);
    closed = true;
  }

  /**
   * Dumps the optimized objectives and the constraints on the solver in the SMT-lib format.
   * Super-useful!
   */
  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.optimizeToString(z3context, z3optContext);
  }
}
