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

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;

class Z3QuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final Z3FormulaCreator z3FormulaCreator;

  Z3QuantifiedFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
    z3FormulaCreator = creator;
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> pVariables, Long pBody) {
    if (pVariables.isEmpty()) {
      throw new IllegalArgumentException("List of quantified variables can not be empty");
    }
    return Native.mkQuantifierConst(
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

    return z3FormulaCreator.applyTactics(z3context, pExtractInfo, "qe-light", "qe");
  }
}
