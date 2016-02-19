/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_numeral_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_optimize;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_params;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_string_symbol;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_assert;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_check;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_get_lower;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_get_model;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_get_reason_unknown;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_get_upper;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_maximize;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_minimize;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_pop;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_push;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_set_params;
import static org.sosy_lab.solver.z3.Z3NativeApi.optimize_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.params_set_symbol;
import static org.sosy_lab.solver.z3.Z3NativeApi.simplify;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.RationalFormulaManager;
import org.sosy_lab.solver.z3.Z3Formula.Z3RationalFormula;
import org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_LBOOL;

import java.util.logging.Level;

import javax.annotation.Nullable;

class Z3OptimizationProver extends Z3AbstractProver<Void> implements OptimizationProverEnvironment {

  private final FormulaManager mgr;
  private final RationalFormulaManager rfmgr;
  private final LogManager logger;
  private static final String Z3_INFINITY_REPRESENTATION = "oo";
  private final long z3optContext;

  Z3OptimizationProver(
      FormulaManager mgr,
      Z3FormulaCreator creator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(creator, pShutdownNotifier);
    this.mgr = mgr;
    rfmgr = mgr.getRationalFormulaManager();
    z3optContext = mk_optimize(z3context);
    optimize_inc_ref(z3context, z3optContext);
    logger = pLogger;
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    long z3Constraint = creator.extractInfo(constraint);
    optimize_assert(z3context, z3optContext, z3Constraint);
    return null;
  }

  @Override
  public int maximize(Formula objective) {
    Preconditions.checkState(!closed);
    Z3Formula z3Objective = (Z3Formula) objective;
    return optimize_maximize(z3context, z3optContext, z3Objective.getFormulaInfo());
  }

  @Override
  public int minimize(Formula objective) {
    Preconditions.checkState(!closed);
    Z3Formula z3Objective = (Z3Formula) objective;
    return optimize_minimize(z3context, z3optContext, z3Objective.getFormulaInfo());
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    try {
      int status = optimize_check(z3context, z3optContext);
      if (status == Z3_LBOOL.Z3_L_FALSE.status) {
        return OptStatus.UNSAT;
      } else if (status == Z3_LBOOL.Z3_L_UNDEF.status) {
        logger.log(
            Level.INFO,
            "Solver returned an unknown status, explanation: ",
            optimize_get_reason_unknown(z3context, z3optContext));
        return OptStatus.UNDEF;
      } else {
        return OptStatus.OPT;
      }
    } catch (Z3SolverException e) {
      // check if it's a timeout
      shutdownNotifier.shutdownIfNecessary();
      throw e;
    }
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    optimize_push(z3context, z3optContext);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    optimize_pop(z3context, z3optContext);
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    return check() == OptStatus.UNSAT;
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    Preconditions.checkState(!closed);
    long ast = optimize_get_upper(z3context, z3optContext, handle);
    if (isInfinity(ast)) {
      return Optional.absent();
    }
    return Optional.of(rationalFromZ3AST(replaceEpsilon(ast, epsilon)));
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    Preconditions.checkState(!closed);
    long ast = optimize_get_lower(z3context, z3optContext, handle);
    if (isInfinity(ast)) {
      return Optional.absent();
    }
    return Optional.of(rationalFromZ3AST(replaceEpsilon(ast, epsilon)));
  }

  @Override
  protected long getZ3Model() {
    return optimize_get_model(z3context, z3optContext);
  }

  void setParam(String key, String value) {
    long keySymbol = mk_string_symbol(z3context, key);
    long valueSymbol = mk_string_symbol(z3context, value);
    long params = mk_params(z3context);
    params_set_symbol(z3context, params, keySymbol, valueSymbol);
    optimize_set_params(z3context, z3optContext, params);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    optimize_dec_ref(z3context, z3optContext);
    closed = true;
  }

  private boolean isInfinity(long ast) {
    return ast_to_string(z3context, ast).contains(Z3_INFINITY_REPRESENTATION);
  }

  /**
   * Replace the epsilon in the returned formula with a numeric value.
   */
  private long replaceEpsilon(long ast, Rational newValue) {
    Z3Formula z = new Z3RationalFormula(z3context, ast);

    Z3Formula epsFormula = (Z3Formula) rfmgr.makeVariable("epsilon");

    Z3Formula out =
        mgr.substitute(
            z,
            ImmutableMap.<Formula, Formula>of(epsFormula, rfmgr.makeNumber(newValue.toString())));
    return simplify(z3context, out.getFormulaInfo());
  }

  private Rational rationalFromZ3AST(long ast) {
    return Rational.ofString(get_numeral_string(z3context, ast));
  }

  /**
   * Dumps the optimized objectives and the constraints on the solver in the
   * SMT-lib format. Super-useful!
   */
  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return optimize_to_string(z3context, z3optContext);
  }
}
