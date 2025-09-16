// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC5Model extends AbstractModel<Term, Sort, TermManager> {
  private final ImmutableList<ValueAssignment> model;
  private final Solver solver;

  CVC5Model(
      FormulaManager pFormulaManager, CVC5AbstractProver<?> pProver, CVC5FormulaCreator pCreator) {
    super(pFormulaManager, pProver, pCreator);
    solver = pProver.solver;

    // We need to generate and save this at construction time as CVC5 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = super.asList();
  }

  @Override
  public Term evalImpl(Term f) {
    Preconditions.checkState(!isClosed());
    return solver.getValue(f);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
