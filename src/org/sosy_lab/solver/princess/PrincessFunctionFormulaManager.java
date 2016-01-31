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
import static com.google.common.collect.FluentIterable.from;

import ap.parser.IExpression;
import ap.parser.IFunction;

import com.google.common.base.Predicates;

import org.sosy_lab.solver.basicimpl.AbstractFunctionFormulaManager;

import java.util.List;

class PrincessFunctionFormulaManager
    extends AbstractFunctionFormulaManager<
        IExpression, IFunction, PrincessTermType, PrincessEnvironment> {

  private final PrincessFormulaCreator creator;

  PrincessFunctionFormulaManager(PrincessFormulaCreator creator) {
    super(creator);
    this.creator = creator;
  }

  @Override
  protected IExpression createUninterpretedFunctionCallImpl(
      IFunction pFuncDecl, List<IExpression> pArgs) {
    return creator.makeFunction(pFuncDecl, pArgs);
  }

  @Override
  protected IFunction declareUninterpretedFunctionImpl(
      String pName, PrincessTermType pReturnType, List<PrincessTermType> args) {
    checkArgument(
        pReturnType == PrincessTermType.Integer || pReturnType == PrincessTermType.Boolean,
        "Princess does not support return types of UFs other than Integer");
    checkArgument(
        from(args).allMatch(Predicates.equalTo(PrincessTermType.Integer)),
        "Princess does not support argument types of UFs other than Integer");

    return getFormulaCreator().getEnv().declareFun(pName, args.size(), pReturnType);
  }
}
