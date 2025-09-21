// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value_as_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_model_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_function;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class Yices2Model extends AbstractModel<Integer, Integer, Long> {

  private final long model;

  private final ImmutableList<ValueAssignment> assignments;

  Yices2Model(
      FormulaManager pFormulaManager,
      long pModel,
      Yices2TheoremProver pProver,
      Yices2FormulaCreator pCreator) {
    super(pFormulaManager, pProver, pCreator);
    model = pModel;
    assignments = super.asList();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return assignments;
  }

  @Override
  public void close() {
    if (!isClosed()) {
      yices_free_model(model);
    }
    super.close();
  }

  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    Preconditions.checkState(!isClosed());
    if (yices_term_is_function(pFormula)) {
      // Yices can't evaluate Uf or array terms. We will simply return the term itself
      // TODO Is this always a good idea?
      return pFormula;
    }

    return yices_get_value_as_term(model, pFormula);
  }

  @Override
  public String toString() {
    return yices_model_to_string(model);
  }
}
