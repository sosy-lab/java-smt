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
import static scala.collection.JavaConversions.iterableAsScalaIterable;

import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IQuantified;
import ap.terfor.ConstantTerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.conjunctions.Quantifier.EX$;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.List;

public class PrincessQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<IExpression, PrincessTermType, PrincessEnvironment,
    PrincessFunctionDeclaration> {

  private final PrincessEnvironment env;

  protected PrincessQuantifiedFormulaManager(
      FormulaCreator<IExpression,
          PrincessTermType, PrincessEnvironment, PrincessFunctionDeclaration> pCreator) {
    super(pCreator);
    env = getFormulaCreator().getEnv();
  }

  @Override
  protected IExpression exists(List<IExpression> pVariables, IExpression pBody) {
    return mkQuantifier(Quantifier.EXISTS, pVariables, pBody);
  }

  @Override
  protected IExpression forall(List<IExpression> pVariables, IExpression pBody) {
    return mkQuantifier(Quantifier.FORALL, pVariables, pBody);
  }

  @Override
  public IExpression mkQuantifier(Quantifier q, List<IExpression> vars, IExpression body) {
    checkArgument(body instanceof IFormula);
    ap.terfor.conjunctions.Quantifier pq = (q == Quantifier.FORALL) ? ALL$.MODULE$ : EX$.MODULE$;
    if (vars.size() == 0) {

      // Body already contains bound variables.
      return new IQuantified(pq, (IFormula) body);
    } else {
      return IExpression.quanConsts(
          pq, iterableAsScalaIterable(toConstantTerm(vars)), (IFormula) body);
    }
  }

  private List<ConstantTerm> toConstantTerm(List<IExpression> lst) {
    List<ConstantTerm> retVal = new ArrayList<>(lst.size());
    for (IExpression f : lst) {
      retVal.add(((IConstant) f).c());
    }
    return retVal;
  }

  @Override
  protected IExpression eliminateQuantifiers(IExpression formula)
      throws SolverException, InterruptedException {
    checkArgument(formula instanceof IFormula);
    return env.elimQuantifiers((IFormula) formula);
  }
}
