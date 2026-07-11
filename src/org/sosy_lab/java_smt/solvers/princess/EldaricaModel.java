/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class EldaricaModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final Map<Predicate, IFormula> model;

  EldaricaModel(
      Map<Predicate, IFormula> pModel, EldaricaHornProver prover,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator) {
    super(prover, creator);
    model = pModel;
  }

  private ImmutableList<ValueAssignment> getAssignments(Predicate predicate, IFormula formula) {
    // TODO: "{fun/2=(((-91 + _1) >= 0) & (((91 + -1 * _1) >= 0) | (((-10 + (_0 + -1 * _1)) >= 0) & ((-102 + _0) >= 0))))}"

    var encapsulated = creator.encapsulateWithTypeOf(formula);


    var assignment = new ValueAssignment(
        encapsulated,
        encapsulated,
        creator.encapsulateBoolean(formula),
        predicate.name(),
        formula,
        new ArrayList<>()
        );

    return ImmutableList.of(assignment);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();

    for (var entry : model.entrySet()) {
      assignments.addAll(getAssignments(entry.getKey(), entry.getValue()));
    }

    return assignments.build().asList();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    throw new UnsupportedOperationException(); // TODO?
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
