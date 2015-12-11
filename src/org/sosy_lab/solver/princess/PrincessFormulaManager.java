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
package org.sosy_lab.solver.princess;

import static com.google.common.collect.Iterables.getOnlyElement;

import ap.parser.BooleanCompactifier;
import ap.parser.IExpression;
import ap.parser.IFormula;

import ap.parser.PartialEvaluator;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;

import javax.annotation.Nullable;

public final class PrincessFormulaManager
    extends AbstractFormulaManager<IExpression, TermType, PrincessEnvironment> {

  @Options(prefix = "solver.princess")
  static class PrincessOptions {
    @Option(
      secure = true,
      description =
          "The number of atoms a term has to have before"
              + " it gets abbreviated if there are more identical terms."
    )
    private int minAtomsForAbbreviation = 100;

    PrincessOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    public int getMinAtomsForAbbreviation() {
      return minAtomsForAbbreviation;
    }
  }

  private final ShutdownNotifier shutdownNotifier;

  @SuppressWarnings("checkstyle:parameternumber")
  private PrincessFormulaManager(
      PrincessFormulaCreator pCreator,
      PrincessUnsafeFormulaManager pUnsafeManager,
      PrincessFunctionFormulaManager pFunctionManager,
      PrincessBooleanFormulaManager pBooleanManager,
      PrincessIntegerFormulaManager pIntegerManager,
      PrincessArrayFormulaManager pArrayManager,
      PrincessQuantifiedFormulaManager pQuantifierManager,
      ShutdownNotifier pShutdownNotifier) {
    super(
        pCreator,
        pUnsafeManager,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        null,
        null,
        null,
        pQuantifierManager,
        pArrayManager);
    shutdownNotifier = pShutdownNotifier;
  }

  public static PrincessFormulaManager create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pLogfileTemplate,
      boolean pUseNonLinearIntegerArithmetic)
      throws InvalidConfigurationException {

    PrincessOptions options = new PrincessOptions(config);

    PrincessEnvironment env = new PrincessEnvironment(pLogfileTemplate, pShutdownNotifier, options);

    PrincessFormulaCreator creator =
        new PrincessFormulaCreator(env, TermType.Boolean, TermType.Integer);

    // Create managers
    PrincessUnsafeFormulaManager unsafeManager = new PrincessUnsafeFormulaManager(creator);
    PrincessFunctionFormulaManager functionTheory = new PrincessFunctionFormulaManager(creator);
    PrincessBooleanFormulaManager booleanTheory = new PrincessBooleanFormulaManager(creator);
    PrincessIntegerFormulaManager integerTheory =
        new PrincessIntegerFormulaManager(creator, functionTheory, pUseNonLinearIntegerArithmetic);
    PrincessArrayFormulaManager arrayTheory = new PrincessArrayFormulaManager(creator);
    PrincessQuantifiedFormulaManager quantifierTheory =
        new PrincessQuantifiedFormulaManager(creator);

    return new PrincessFormulaManager(
        creator,
        unsafeManager,
        functionTheory,
        booleanTheory,
        integerTheory,
        arrayTheory,
        quantifierTheory,
        pShutdownNotifier);
  }

  BooleanFormula encapsulateBooleanFormula(IExpression t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public ProverEnvironment newProverEnvironment(
      boolean pGenerateModels, boolean pGenerateUnsatCore) {
    return new PrincessTheoremProver(this, shutdownNotifier);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(boolean pShared) {
    return new PrincessInterpolatingProver(this);
  }

  @Override
  public OptEnvironment newOptEnvironment() {
    throw new UnsupportedOperationException("Princess does not support optimization");
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    return encapsulateBooleanFormula(getOnlyElement(getEnvironment().parseStringToTerms(pS)));
  }

  @Override
  public Appender dumpFormula(final IExpression formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return getEnvironment().dumpFormula((IFormula) formula);
  }

  @Override
  public String getVersion() {
    return getEnvironment().getVersion();
  }

  @Override
  protected IExpression simplify(IExpression f) {
    // TODO this method is not tested, check it!
    if (f instanceof IFormula) {
      f = BooleanCompactifier.apply((IFormula) f);
    }
    return PartialEvaluator.apply(f);
  }
}
