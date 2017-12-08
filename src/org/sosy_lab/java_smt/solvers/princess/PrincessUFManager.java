/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;

import ap.parser.IExpression;
import ap.types.Sort;
import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIFunctionDeclaration;

class PrincessUFManager
    extends AbstractUFManager<
        IExpression, PrincessFunctionDeclaration, Sort, PrincessEnvironment> {

  private final PrincessFormulaCreator creator;

  PrincessUFManager(PrincessFormulaCreator creator) {
    super(creator);
    this.creator = creator;
  }

  @Override
  protected IExpression createUninterpretedFunctionCallImpl(
      PrincessFunctionDeclaration pFuncDecl, List<IExpression> pArgs) {
    return creator.makeFunction(pFuncDecl, pArgs);
  }

  @Override
  protected PrincessFunctionDeclaration declareUninterpretedFunctionImpl(
      String pName, Sort pReturnType, List<Sort> args) {
    return new PrincessIFunctionDeclaration(
        getFormulaCreator().getEnv().declareFun(pName, pReturnType, args));
  }
}
