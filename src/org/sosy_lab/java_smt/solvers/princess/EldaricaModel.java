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

import ap.api.SimpleAPI;
import ap.parser.IBinFormula;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IPlus;
import ap.parser.ISortedVariable;
import ap.parser.ITerm;
import ap.parser.ITimes;
import ap.terfor.preds.Predicate;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Map;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import scala.collection.JavaConverters;

public class EldaricaModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final Map<Predicate, IFormula> model;
  private final SimpleAPI api = SimpleAPI.spawn();

  EldaricaModel(
      Map<Predicate, IFormula> pModel, EldaricaHornProver prover,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator) {
    super(prover, creator);
    model = pModel;
  }

  private ImmutableList<ValueAssignment> getAssignments(Predicate predicate, IFormula formula) {
    var encapsulated = creator.encapsulateWithTypeOf(formula);


    var assignment = new ValueAssignment(
        encapsulated,
        encapsulated,
        creator.encapsulateBoolean(formula),
        predicate.name(),
        evalAssignments(formula),
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

  private ITerm toPrincess(ITerm term) {
    if (term instanceof IPlus plus) {
      return new IPlus(toPrincess(plus.t1()), toPrincess(plus.t2()));
    }
    if (term instanceof ITimes times) {
      return new ITimes(times.coeff(), toPrincess(times.subterm()));
    }
    if (term instanceof IIntLit lit) {
      return lit;
    }
    if (term instanceof IConstant constant) {
      return constant;
    }
    if (term instanceof ISortedVariable variable) {
      return api.createConstant("_" + variable.index(), variable.sort());
    }

    throw new IllegalArgumentException("Unhandled model term: " + term);
  }

  private IFormula toPrincess(IFormula formula) {
    if (formula instanceof IBinFormula bin) {
      return new IBinFormula(bin.j(), toPrincess(bin.f1()),
          toPrincess(bin.f2()));
    }
    if (formula instanceof IIntFormula _int) {
      return new IIntFormula(_int.rel(), toPrincess(_int.t()));
    }
    if (formula instanceof IBoolLit bool) {
      return bool;
    }
    throw new IllegalArgumentException("Unhandled model formula: " + formula);
  }

  private Object toValue(IExpression expression) {
    if (expression instanceof IIntLit lit) {
      return lit.value().bigIntValue();
    }
    if (expression instanceof IBoolLit lit) {
      return lit.value();
    }


    throw new IllegalArgumentException("Unhandled model value: " + expression);
  }

  private Object[] evalAssignments(IFormula formula) {
    var converted = toPrincess(formula);
    if (formula instanceof IBoolLit lit && lit.isFalse()) {
      return new Object[]{false};
    }

    api.addAssertion(converted);
    api.checkSat(true);
    var model = api.partialModel().interpretation();

    var output = new Object[model.size()];

    for (var tuple : JavaConverters.asJava(model.view())) {
      output[Integer.parseInt(((IConstant) tuple._1).c().name().substring(1))] = toValue(tuple._2);
    }

    return output;
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    throw new UnsupportedOperationException();
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
