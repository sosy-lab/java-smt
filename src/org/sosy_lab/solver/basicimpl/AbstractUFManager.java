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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.collect.FluentIterable.from;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.UFManager;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * This class simplifies the implementation of the FunctionFormulaManager by converting the types
 * to the solver specific type.
 *
 * @param <TFormulaInfo> The solver specific type.
 * @param <TFunctionDecl> The solver specific type of declarations of any function application
 * @param <TType> The solver specific type of formula-types.
 */
public abstract class AbstractUFManager<TFormulaInfo, TFunctionDecl, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFunctionDecl>
    implements UFManager {

  protected AbstractUFManager(FormulaCreator<TFormulaInfo, TType, TEnv, TFunctionDecl> pCreator) {
    super(pCreator);
  }

  protected abstract TFunctionDecl declareUninterpretedFunctionImpl(
      String pName, TType pReturnType, List<TType> pArgTypes);

  @Override
  public final <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    checkArgument(
        !pArgTypes.contains(FormulaType.BooleanType),
        "Uninterpreted functions with boolean arguments are currently not supported in JavaSMT.");

    List<TType> argTypes = new ArrayList<>(pArgTypes.size());
    for (FormulaType<?> argtype : pArgTypes) {
      argTypes.add(toSolverType(argtype));
    }

    return FunctionDeclarationImpl.of(
        pName,
        FunctionDeclarationKind.UF,
        pArgTypes,
        pReturnType,
        declareUninterpretedFunctionImpl(pName, toSolverType(pReturnType), argTypes));
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {

    return declareUF(pName, pReturnType, Arrays.asList(pArgs));
  }

  protected abstract TFormulaInfo createUninterpretedFunctionCallImpl(
      TFunctionDecl func, List<TFormulaInfo> pArgs);

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return formulaCreator.callFunction(funcType, ImmutableList.copyOf(args));
  }

  @Override
  public final <T extends Formula> T callUF(
      FunctionDeclaration<T> pFunc, List<? extends Formula> pArgs) {
    return formulaCreator.callFunction(pFunc, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {

    List<FormulaType<?>> argTypes =
        from(pArgs)
            .transform(
                new Function<Formula, FormulaType<?>>() {
                  @Override
                  public FormulaType<?> apply(Formula pArg0) {
                    return getFormulaCreator().getFormulaType(pArg0);
                  }
                })
            .toList();
    FunctionDeclaration<T> func = declareUF(name, pReturnType, argTypes);
    return callUF(func, pArgs);
  }
}
