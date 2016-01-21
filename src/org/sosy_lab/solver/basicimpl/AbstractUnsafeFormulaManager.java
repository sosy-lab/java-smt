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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.Lists;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.UnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.List;

public abstract class AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv> implements UnsafeFormulaManager {

  protected AbstractUnsafeFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv> creator) {
    super(creator);
  }

  private <T extends Formula> T encapsulateWithTypeOf(T f, TFormulaInfo e) {
    FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator = getFormulaCreator();
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), e);
  }

  @Override
  public int getArity(Formula pF) {
    TFormulaInfo t = extractInfo(pF);
    return getArity(t);
  }

  protected abstract int getArity(TFormulaInfo pT);

  @Override
  public Formula getArg(Formula pF, int pN) {
    assert 0 <= pN && pN < getArity(pF)
        : String.format("index %d out of bounds %d", pN, getArity(pF));
    TFormulaInfo t = extractInfo(pF);
    TFormulaInfo arg = getArg(t, pN);
    FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator = getFormulaCreator();
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(arg), arg);
  }

  protected abstract TFormulaInfo getArg(TFormulaInfo pT, int n);

  protected abstract boolean isVariable(TFormulaInfo pT);

  @Override
  public <T extends Formula> T replaceArgsAndName(T f, String newName, List<Formula> args) {
    return encapsulateWithTypeOf(
        f, replaceArgsAndName(extractInfo(f), newName, Lists.transform(args, extractor)));
  }

  protected abstract TFormulaInfo replaceArgsAndName(
      TFormulaInfo pT, String newName, List<TFormulaInfo> newArgs);

  @Override
  public <T extends Formula> T replaceArgs(T pF, List<Formula> pArgs) {
    assert pArgs.size() == getArity(pF) : "number of args must match arity.";
    return encapsulateWithTypeOf(
        pF, replaceArgs(extractInfo(pF), Lists.transform(pArgs, extractor)));
  }

  protected abstract TFormulaInfo replaceArgs(TFormulaInfo pT, List<TFormulaInfo> newArgs);

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula input) {
    return visit(visitor, input, getFormulaCreator().extractInfo(input));
  }

  protected abstract <R> R visit(FormulaVisitor<R> visitor, Formula input, TFormulaInfo f);

  protected void visitRecursively(FormulaVisitor<TraversalProcess> pFormulaVisitor, Formula pF) {
    RecursiveFormulaVisitor recVisitor = new RecursiveFormulaVisitor(pFormulaVisitor);
    recVisitor.addToQueue(pF);
    while (!recVisitor.isQueueEmpty()) {
      TraversalProcess process = checkNotNull(visit(recVisitor, recVisitor.pop()));
      if (process == TraversalProcess.ABORT) {
        return;
      }
    }
  }
}
