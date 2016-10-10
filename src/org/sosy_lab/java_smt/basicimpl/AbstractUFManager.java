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
package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.Lists;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.UFManager;

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

    List<TType> argTypes = Lists.transform(pArgTypes, this::toSolverType);

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
    return formulaCreator.callFunction(funcType, Arrays.asList(args));
  }

  @Override
  public final <T extends Formula> T callUF(
      FunctionDeclaration<T> pFunc, List<? extends Formula> pArgs) {
    return formulaCreator.callFunction(pFunc, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    List<FormulaType<?>> argTypes = Lists.transform(pArgs, getFormulaCreator()::getFormulaType);
    FunctionDeclaration<T> func = declareUF(name, pReturnType, argTypes);
    return callUF(func, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    return declareAndCallUF(name, pReturnType, Arrays.asList(pArgs));
  }
}
