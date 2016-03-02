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

import com.google.common.primitives.Longs;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.basicimpl.AbstractQuantifiedFormulaManager;

import java.util.List;

class Z3QuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3QuantifiedFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected Long exists(List<Long> pVariables, Long pBody) {
    return mkQuantifier(Quantifier.EXISTS, pVariables, pBody);
  }

  @Override
  protected Long forall(List<Long> pVariables, Long pBody) {
    return mkQuantifier(Quantifier.FORALL, pVariables, pBody);
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> pVariables, Long pBody) {
    return Z3NativeApi.mk_quantifier_const(
        z3context,
        q == Quantifier.FORALL,
        0,
        pVariables.size(),
        Longs.toArray(pVariables),
        0,
        new long[0],
        pBody);
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    // It is recommended (personal communication with Nikolaj Bjorner)
    // to run "qe-light" before "qe".
    // "qe" does not perform a "qe-light" as a preprocessing on its own!

    // One might want to run the tactic "ctx-solver-simplify" on the result.

    return Z3NativeApiHelpers.applyTactics(z3context, pExtractInfo, "qe-light", "qe");
  }
}
