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

import static com.google.common.base.Preconditions.checkArgument;

import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IQuantified;
import ap.parser.ITerm;
import ap.terfor.conjunctions.Quantifier;

import com.google.common.base.Preconditions;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

public class PrincessQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<IExpression, TermType, PrincessEnvironment> {

  private final PrincessEnvironment env;

  protected PrincessQuantifiedFormulaManager(
      FormulaCreator<IExpression, TermType, PrincessEnvironment> pCreator) {
    super(pCreator);
    env = getFormulaCreator().getEnv();
  }

  @Override
  protected IExpression exists(List<IExpression> pVariables, IExpression pBody) {
    checkArgument(pBody instanceof IFormula);
    Set<IExpression> vars = PrincessUtil.getVarsAndUIFs(Collections.singleton(pBody));
    List<ITerm> normalVariables = new ArrayList<>();
    for (IExpression var : vars) {
      if (var instanceof ITerm && !pVariables.contains(var)) {
        normalVariables.add((ITerm) var);
      }
    }
    return env.makeExists(normalVariables, (IFormula) pBody);
  }

  @Override
  protected IExpression forall(List<IExpression> pVariables, IExpression pBody) {
    checkArgument(pBody instanceof IFormula);
    return env.makeForAll(castToITerm(pVariables), (IFormula) pBody);
  }

  private List<ITerm> castToITerm(List<IExpression> lst) {
    List<ITerm> retVal = new ArrayList<>(lst.size());
    for (IExpression f : lst) {
      retVal.add((ITerm) f);
    }
    return retVal;
  }

  @Override
  protected IExpression eliminateQuantifiers(IExpression formula)
      throws SolverException, InterruptedException {
    checkArgument(formula instanceof IFormula);
    return env.elimQuantifiers((IFormula) formula);
  }

  @Override
  protected boolean isQuantifier(IExpression pExtractInfo) {
    return pExtractInfo instanceof IQuantified;
  }

  @Override
  protected boolean isForall(IExpression pExtractInfo) {
    return isQuantifier(pExtractInfo)
        && ((IQuantified) pExtractInfo).quan().equals(Quantifier.apply(true));
  }

  @Override
  protected boolean isExists(IExpression pExtractInfo) {
    return isQuantifier(pExtractInfo)
        && ((IQuantified) pExtractInfo).quan().equals(Quantifier.apply(false));
  }

  @Override
  protected int numQuantifierBound(IExpression pExtractInfo) {
    // TODO implement
    throw new UnsupportedOperationException("Currently not implemented");
  }

  @Override
  protected IExpression getQuantifierBody(IExpression pExtractInfo) {
    Preconditions.checkState(isQuantifier(pExtractInfo));
    return ((IQuantified) pExtractInfo).subformula();
  }

  @Override
  public boolean isBoundByQuantifier(IExpression pF) {
    // TODO implement
    throw new UnsupportedOperationException("Currently not implemented");
  }
}
