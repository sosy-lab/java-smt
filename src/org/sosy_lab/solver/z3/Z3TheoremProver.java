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

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_vector_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.ast_vector_get;
import static org.sosy_lab.solver.z3.Z3NativeApi.ast_vector_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.ast_vector_size;
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_and;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_not;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_solver;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_assert;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_assert_and_track;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_check;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_get_model;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_get_num_scopes;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_get_unsat_core;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_pop;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_push;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_set_params;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FALSE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.isOP;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;
import org.sosy_lab.solver.basicimpl.LongArrayBackedList;
import org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_LBOOL;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;

class Z3TheoremProver extends Z3AbstractProver<Void> implements ProverEnvironment {

  private final ShutdownNotifier shutdownNotifier;
  private final long z3solver;
  private int level = 0;
  private final UniqueIdGenerator trackId = new UniqueIdGenerator();
  private final FormulaManager mgr;

  private static final String UNSAT_CORE_TEMP_VARNAME = "UNSAT_CORE_%d";

  private final @Nullable Map<String, BooleanFormula> storedConstraints;

  Z3TheoremProver(
      Z3FormulaCreator creator,
      Z3FormulaManager pMgr,
      long z3params,
      ShutdownNotifier pShutdownNotifier,
      ProverOptions... options) {
    super(creator);
    mgr = pMgr;
    z3solver = mk_solver(z3context);
    solver_inc_ref(z3context, z3solver);
    solver_set_params(z3context, z3solver, z3params);
    Set<ProverOptions> opts = Sets.newHashSet(options);
    if (opts.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      storedConstraints = new HashMap<>();
    } else {
      storedConstraints = null;
    }
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(solver_get_num_scopes(z3context, z3solver) >= 1);
    level--;
    solver_pop(z3context, z3solver, 1);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    long e = Z3FormulaManager.getZ3Expr(f);
    inc_ref(z3context, e);

    if (storedConstraints != null) { // Unsat core generation is on.
      String varName = String.format(UNSAT_CORE_TEMP_VARNAME, trackId.getFreshId());
      BooleanFormula t = mgr.getBooleanFormulaManager().makeVariable(varName);

      solver_assert_and_track(z3context, z3solver, e, creator.extractInfo(t));
      storedConstraints.put(varName, f);
    } else {
      solver_assert(z3context, z3solver, e);
    }
    dec_ref(z3context, e);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    solver_push(z3context, z3solver);
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    int result = solver_check(z3context, z3solver);
    shutdownNotifier.shutdownIfNecessary();
    Preconditions.checkArgument(result != Z3_LBOOL.Z3_L_UNDEF.status);
    return result == Z3_LBOOL.Z3_L_FALSE.status;
  }

  @Override
  protected long getZ3Model() {
    return solver_get_model(z3context, z3solver);
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return Z3Model.parseZ3Model(z3context, getZ3Model());
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    if (storedConstraints == null) {
      throw new UnsupportedOperationException(
          "Option to generate the UNSAT core wasn't enabled when creating"
              + " the prover environment.");
    }

    List<BooleanFormula> constraints = new ArrayList<>();
    long unsatCore = solver_get_unsat_core(z3context, z3solver);
    ast_vector_inc_ref(z3context, unsatCore);
    for (int i = 0; i < ast_vector_size(z3context, unsatCore); i++) {
      long ast = ast_vector_get(z3context, unsatCore, i);
      BooleanFormula f = creator.encapsulateBoolean(ast);

      constraints.add(storedConstraints.get(mgr.getUnsafeFormulaManager().getName(f)));
    }
    ast_vector_dec_ref(z3context, unsatCore);
    return constraints;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        solver_get_num_scopes(z3context, z3solver) >= 0,
        "a negative number of scopes is not allowed");

    while (level > 0) {
      pop();
    }
    solver_dec_ref(z3context, z3solver);

    closed = true;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // Unpack formulas to terms.
    long[] importantFormulas = new long[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantFormulas[i++] = Z3FormulaManager.getZ3Expr(impF);
    }

    solver_push(z3context, z3solver);

    while (solver_check(z3context, z3solver) == Z3_LBOOL.Z3_L_TRUE.status) {
      long[] valuesOfModel = new long[importantFormulas.length];
      long z3model = solver_get_model(z3context, z3solver);

      for (int j = 0; j < importantFormulas.length; j++) {
        long funcDecl = get_app_decl(z3context, importantFormulas[j]);
        long valueOfExpr = model_get_const_interp(z3context, z3model, funcDecl);

        if (isOP(z3context, valueOfExpr, Z3_OP_FALSE)) {
          valuesOfModel[j] = mk_not(z3context, importantFormulas[j]);
          inc_ref(z3context, valuesOfModel[j]);
        } else {
          valuesOfModel[j] = importantFormulas[j];
        }
      }

      callback.apply(
          new LongArrayBackedList<BooleanFormula>(valuesOfModel) {
            @Override
            protected BooleanFormula convert(long pE) {
              return creator.encapsulateBoolean(pE);
            }
          });

      long negatedModel = mk_not(z3context, mk_and(z3context, valuesOfModel));
      inc_ref(z3context, negatedModel);
      solver_assert(z3context, z3solver, negatedModel);
    }

    // we pushed some levels on assertionStack, remove them and delete solver
    solver_pop(z3context, z3solver, 1);
    return callback.getResult();
  }
}
