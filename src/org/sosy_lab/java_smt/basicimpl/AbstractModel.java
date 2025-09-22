// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractModel<TFormulaInfo, TType, TEnv>
    extends AbstractEvaluator<TFormulaInfo, TType, TEnv> implements Model {

  private final FormulaManager mgr;
  private final AbstractProver<?> prover;

  protected AbstractModel(
      FormulaManager pFormulaManager,
      AbstractProver<?> pProverEnvironment,
      FormulaCreator<TFormulaInfo, TType, TEnv, ?> pFormulaCreator) {
    super(pProverEnvironment, pFormulaCreator);
    prover = pProverEnvironment;
    mgr = pFormulaManager;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    var modelBuilder = new ModelBuilder(mgr);

    ImmutableSet.Builder<TFormulaInfo> extractBuilder = ImmutableSet.builder();
    for (var asserted : prover.getAssertedFormulas()) {
      creator.extractVariablesAndUFs(
          asserted,
          false,
          (name, formula) -> {
            extractBuilder.add(creator.extractInfo(formula));
          });
    }
    var symbols = extractBuilder.build();

    var arrayIndices =
        modelBuilder.collectArrayValues(
            creator.encapsulateBoolean(
                creator.extractInfo(
                    mgr.getBooleanFormulaManager().and(prover.getAssertedFormulas()))),
            f -> eval(f));

    ImmutableList.Builder<ValueAssignment> builder = ImmutableList.builder();
    for (var variable : symbols) {
      if (creator.getFormulaType(variable).isArrayType()) {
        var value = evalImpl(variable);
        if (value != null) {
          builder.addAll(
              modelBuilder.buildArrayAssignments(
                  arrayIndices,
                  (ArrayFormula<?, ?>) creator.encapsulateWithTypeOf(variable),
                  creator.encapsulateWithTypeOf(value)));
        }
      } else {
        var value = evalImpl(variable);
        if (value != null) {
          builder.addAll(
              modelBuilder.buildVariableAssignment(
                  creator.encapsulateWithTypeOf(variable), creator.encapsulateWithTypeOf(value)));
        }
      }
    }
    for (var asserted : prover.getAssertedFormulas()) {
      builder.addAll(
          modelBuilder.buildUfAssignments(
              creator.encapsulateBoolean(creator.extractInfo(asserted)), f -> eval(f)));
    }
    return builder.build();
  }

  @Override
  public String toString() {
    return Joiner.on('\n').join(iterator());
  }
}
