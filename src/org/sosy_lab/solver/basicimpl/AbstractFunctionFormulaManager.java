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
import com.google.common.collect.Lists;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionFormulaManager;
import org.sosy_lab.solver.api.UfDeclaration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * This class simplifies the implementation of the FunctionFormulaManager by converting the types
 * to the solver specific type.
 * It depends on UnsafeFormulaManager to make clear
 * that the UnsafeFormulaManager should not depend on FunctionFormulaManager.
 * @param <TFormulaInfo> The solver specific type.
 * @param <TFunctionDecl> The solver specific type of declarations of uninterpreted functions
 * @param <TType> The solver specific type of formula-types.
 */
public abstract class AbstractFunctionFormulaManager<TFormulaInfo, TFunctionDecl, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv>
    implements FunctionFormulaManager {

  protected AbstractFunctionFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv> pCreator) {
    super(pCreator);
  }

  protected abstract TFunctionDecl declareUninterpretedFunctionImpl(
      String pName, TType pReturnType, List<TType> pArgTypes);

  @Override
  public final <T extends Formula> UfDeclaration<T> declareUninterpretedFunction(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    checkArgument(
        !pArgTypes.contains(FormulaType.BooleanType),
        "Uninterpreted functions with boolean arguments are currently not supported in JavaSMT.");

    List<TType> argTypes = new ArrayList<>(pArgTypes.size());
    for (FormulaType<?> argtype : pArgTypes) {
      argTypes.add(toSolverType(argtype));
    }

    return new UfDeclarationImpl<>(
        pReturnType,
        declareUninterpretedFunctionImpl(pName, toSolverType(pReturnType), argTypes),
        pArgTypes);
  }

  @Override
  public <T extends Formula> UfDeclaration<T> declareUninterpretedFunction(
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {

    return declareUninterpretedFunction(pName, pReturnType, Arrays.asList(pArgs));
  }

  protected abstract TFormulaInfo createUninterpretedFunctionCallImpl(
      TFunctionDecl func, List<TFormulaInfo> pArgs);

  @Override
  public final <T extends Formula> T callUninterpretedFunction(
      UfDeclaration<T> pFunc, List<? extends Formula> pArgs) {
    FormulaType<T> retType = pFunc.getReturnType();
    List<TFormulaInfo> list = Lists.transform(pArgs, extractor);

    TFormulaInfo formulaInfo = createUninterpretedFunctionCallImpl(pFunc, list);
    return getFormulaCreator().encapsulate(retType, formulaInfo);
  }

  final <T extends Formula> TFormulaInfo createUninterpretedFunctionCallImpl(
      UfDeclaration<T> pFunc, List<TFormulaInfo> pArgs) {
    @SuppressWarnings("unchecked")
    UfDeclarationImpl<T, TFunctionDecl> func = (UfDeclarationImpl<T, TFunctionDecl>) pFunc;

    return createUninterpretedFunctionCallImpl(func.getFuncDecl(), pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUninterpretedFunction(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {

    List<FormulaType<?>> argTypes = from(pArgs).
        transform(
            new Function<Formula, FormulaType<?>>() {
              @Override
              public FormulaType<?> apply(Formula pArg0) {
                return getFormulaCreator().getFormulaType(pArg0);
              }}).toList();
    UfDeclaration<T> func = declareUninterpretedFunction(name, pReturnType, argTypes);
    return callUninterpretedFunction(func, pArgs);
  }
}
