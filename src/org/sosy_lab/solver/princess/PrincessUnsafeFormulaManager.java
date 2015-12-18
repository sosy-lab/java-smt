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
import static java.util.Collections.singleton;
import static org.sosy_lab.solver.princess.PrincessUtil.isBoolean;
import static scala.collection.JavaConversions.iterableAsScalaIterable;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;

import java.util.List;
import java.util.Map;

class PrincessUnsafeFormulaManager
    extends AbstractUnsafeFormulaManager<IExpression, TermType, PrincessEnvironment> {

  PrincessUnsafeFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  public boolean isAtom(IExpression t) {
    return PrincessUtil.isAtom(t);
  }

  @Override
  public int getArity(IExpression pT) {
    return PrincessUtil.getArity(pT);
  }

  @Override
  public IExpression getArg(IExpression pT, int pN) {
    return PrincessUtil.getArg(pT, pN);
  }

  @Override
  public boolean isVariable(IExpression pT) {
    return PrincessUtil.isVariable(pT);
  }

  @Override
  public boolean isUF(IExpression t) {
    return PrincessUtil.isUIF(t);
  }

  @Override
  public String getName(IExpression t) {
    if (isVariable(t)) {
      return t.toString();
    } else if (isUF(t)) {
      return ((IFunApp) t).fun().name();
    } else {
      throw new IllegalArgumentException("The Term " + t + " has no name!");
    }
  }

  @Override
  public IExpression replaceArgs(IExpression pT, List<IExpression> newArgs) {
    return PrincessUtil.replaceArgs(pT, newArgs);
  }

  @Override
  public IExpression replaceArgsAndName(IExpression t, String pNewName, List<IExpression> newArgs) {

    if (isVariable(t)) {
      checkArgument(newArgs.isEmpty());

      // when no new name is given we need to use the old variable
      if (t.toString().equals(pNewName)) {
        return t;
      }

      return getFormulaCreator()
          .makeVariable(isBoolean(t) ? TermType.Boolean : TermType.Integer, pNewName);

    } else if (isUF(t)) {
      IFunApp fun = (IFunApp) t;
      PrincessEnvironment env = getFormulaCreator().getEnv();
      TermType returnType = env.getReturnTypeForFunction(fun.fun());
      return env.makeFunction(env.declareFun(pNewName, fun.args().size(), returnType), newArgs);

    } else {
      throw new IllegalArgumentException("The Term " + t + " has no name!");
    }
  }

  @Override
  public <T1 extends Formula, T2 extends Formula> T1 substitute(T1 pF, Map<T2, T2> pFromToMapping) {
    return substituteUsingMap(pF, pFromToMapping);
  }

  @Override
  protected List<? extends IExpression> splitNumeralEqualityIfPossible(IExpression pF) {
    // Princess does not support Equal.
    // Formulas are converted from "a==b" to "a+(-b)==0".
    if (pF instanceof IIntFormula && ((IIntFormula) pF).rel() == IIntRelation.EqZero()) {
      return ImmutableList.of(
          ((IIntFormula) pF).t().$less$eq(new IIntLit(IdealInt.ZERO())),
          ((IIntFormula) pF).t().$greater$eq(new IIntLit(IdealInt.ZERO())));
    }
    return ImmutableList.of(pF);
  }

  @Override
  public boolean isNumber(IExpression pT) {
    return PrincessUtil.isNumber(pT);
  }

  @Override
  protected boolean isQuantification(IExpression pT) {
    return PrincessUtil.isQuantifier(pT);
  }

  @Override
  protected IExpression getQuantifiedBody(IExpression pT) {
    return PrincessUtil.getQuantifierBody(pT);
  }

  @Override
  protected IExpression replaceQuantifiedBody(IExpression pF, IExpression pBody) {
    Preconditions.checkArgument(isQuantification(pF));
    return pF.update(iterableAsScalaIterable(singleton(pBody)).toSeq());
  }

  @Override
  protected boolean isFreeVariable(IExpression pT) {
    return isVariable(pT);
  }

  @Override
  protected boolean isBoundVariable(IExpression pT) {
    return PrincessUtil.isBoundByQuantifier(pT);
  }
}
