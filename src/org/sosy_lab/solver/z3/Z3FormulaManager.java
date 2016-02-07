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

import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bvuge;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bvule;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_ge;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_le;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_solver;
import static org.sosy_lab.solver.z3.Z3NativeApi.parse_smtlib2_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_assert;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_BV_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_INT_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_EQ;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_REAL_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.isOP;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.primitives.Longs;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;

import java.io.IOException;
import java.util.List;
import java.util.Map;

final class Z3FormulaManager extends AbstractFormulaManager<Long, Long, Long> {

  @SuppressWarnings("checkstyle:parameternumber")
  Z3FormulaManager(
      Z3FormulaCreator pFormulaCreator,
      Z3FunctionFormulaManager pFunctionManager,
      Z3BooleanFormulaManager pBooleanManager,
      Z3IntegerFormulaManager pIntegerManager,
      Z3RationalFormulaManager pRationalManager,
      Z3BitvectorFormulaManager pBitpreciseManager,
      Z3QuantifiedFormulaManager pQuantifiedManager,
      Z3ArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        null,
        pQuantifiedManager,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String str) throws IllegalArgumentException {

    // TODO do we need sorts or decls?
    // the context should know them already,
    // TODO check this
    long[] sortSymbols = new long[0];
    long[] sorts = new long[0];
    long[] declSymbols = new long[0];
    long[] decls = new long[0];
    long e = parse_smtlib2_string(getEnvironment(), str, sortSymbols, sorts, declSymbols, decls);

    return getFormulaCreator().encapsulateBoolean(e);
  }

  static long getZ3Expr(Formula pT) {
    if (pT instanceof Z3Formula) {
      return ((Z3Formula) pT).getFormulaInfo();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  private static final ImmutableMap<Tactic, String> Z3_TACTICS =
      ImmutableMap.<Tactic, String>builder()
          .put(Tactic.NNF, "nnf")
          .put(Tactic.CNF, "cnf")
          .put(Tactic.TSEITIN_CNF, "tseitin-cnf")
          .put(Tactic.QE, "qe")
          .put(Tactic.QE_LIGHT, "qe-light")
          .build();

  @Override
  protected Long applyTacticImpl(Long input, Tactic tactic) throws InterruptedException {
    String z3TacticName = Z3_TACTICS.get(tactic);
    if (z3TacticName != null) {
      return Z3NativeApiHelpers.applyTactic(getFormulaCreator().getEnv(), input, z3TacticName);
    } else {
      return super.applyTacticImpl(input, tactic);
    }
  }

  @Override
  public Appender dumpFormula(final Long expr) {
    assert getFormulaCreator().getFormulaType(expr) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {

        // Serializing a solver is a simplest way to dump a formula in Z3,
        // cf https://github.com/Z3Prover/z3/issues/397
        long z3solver = mk_solver(getEnvironment());
        solver_inc_ref(getEnvironment(), z3solver);
        solver_assert(getEnvironment(), z3solver, expr);
        String serialized = solver_to_string(getEnvironment(), z3solver);
        solver_dec_ref(getEnvironment(), z3solver);
        out.append(serialized);
      }
    };
  }

  @Override
  protected Long simplify(Long pF) {
    return Z3NativeApi.simplify(getFormulaCreator().getEnv(), pF);
  }

  @Override
  protected List<? extends Long> splitNumeralEqualityIfPossible(Long pF) {
    long z3context = getFormulaCreator().getEnv();
    if (isOP(z3context, pF, Z3_OP_EQ) && get_app_num_args(z3context, pF) == 2) {
      long arg0 = get_app_arg(z3context, pF, 0);
      inc_ref(z3context, arg0);
      long arg1 = get_app_arg(z3context, pF, 1);
      inc_ref(z3context, arg1);

      try {
        long sortKind = get_sort_kind(z3context, get_sort(z3context, arg0));
        assert sortKind == get_sort_kind(z3context, get_sort(z3context, arg1));
        if (sortKind == Z3_BV_SORT) {

          long out1 = mk_bvule(z3context, arg0, arg1);
          inc_ref(z3context, out1);
          long out2 = mk_bvuge(z3context, arg0, arg1);
          inc_ref(z3context, out2);

          return ImmutableList.of(out1, out2);
        } else if (sortKind == Z3_INT_SORT || sortKind == Z3_REAL_SORT) {

          long out1 = mk_le(z3context, arg0, arg1);
          inc_ref(z3context, out1);
          long out2 = mk_ge(z3context, arg0, arg1);
          inc_ref(z3context, out2);
          return ImmutableList.of(out1, out2);
        }
      } finally {
        dec_ref(z3context, arg0);
        dec_ref(z3context, arg1);
      }
    }
    return ImmutableList.of(pF);
  }

  @Override
  public <T extends Formula> T substitute(
      T pF, Map<? extends Formula, ? extends Formula> pFromToMapping) {
    return substituteUsingLists(pF, pFromToMapping);
  }

  @Override
  protected Long substituteUsingListsImpl(Long t, List<Long> changeFrom, List<Long> changeTo) {
    int size = changeFrom.size();
    Preconditions.checkState(size == changeTo.size());
    return Z3NativeApi.substitute(
        getFormulaCreator().getEnv(), t, size, Longs.toArray(changeFrom), Longs.toArray(changeTo));
  }

  @Override
  public BooleanFormula translate(BooleanFormula other, SolverContext otherContext) {
    if (otherContext instanceof Z3SolverContext) {
      Z3SolverContext o = (Z3SolverContext) otherContext;
      long otherZ3Context = o.getFormulaManager().getEnvironment();
      if (otherZ3Context == getEnvironment()) {

        // Same context.
        return other;
      } else {

        // Z3-to-Z3 translation.
        long translatedAST =
            Z3NativeApi.translate(otherZ3Context, extractInfo(other), getEnvironment());
        return getFormulaCreator().encapsulateBoolean(translatedAST);
      }
    }
    return super.translate(other, otherContext);
  }
}
