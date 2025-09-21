// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableList;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class SmtInterpolModel extends AbstractModel<Term, Sort, Script> {

  private final Model model;
  private final ImmutableList<ValueAssignment> assignments;

  SmtInterpolModel(
      FormulaManager pFormulaManager,
      AbstractProver<?> pProver,
      Model pModel,
      FormulaCreator<Term, Sort, Script, ?> pCreator) {
    super(pFormulaManager, pProver, pCreator);
    model = pModel;

    assignments = super.asList();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return assignments;
  }

  @Override
  public void close() {}

  @Override
  protected Term evalImpl(Term formula) {
    return model.evaluate(formula);
  }
}
