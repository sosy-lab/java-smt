// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.collect.Lists;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.UFManager;

/**
 * This class simplifies the implementation of the FunctionFormulaManager by converting the types to
 * the solver specific type.
 *
 * @param <TFormulaInfo> The solver specific type.
 * @param <TFunctionDecl> The solver specific type of declarations of any function application
 * @param <TType> The solver specific type of formula-types.
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractUFManager<TFormulaInfo, TFunctionDecl, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFunctionDecl>
    implements UFManager {

  protected AbstractUFManager(FormulaCreator<TFormulaInfo, TType, TEnv, TFunctionDecl> pCreator) {
    super(pCreator);
  }

  @Override
  public final <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    checkVariableName(pName);
    if (Generator.isLoggingEnabled()) {
      // FIXME Find a better way to handle quoted symbols
      if (pName.contains("PIPE")) {
        pName = pName.replaceAll("PIPE", "|");
      }
    }
    List<TType> argTypes = Lists.transform(pArgTypes, this::toSolverType);
    FunctionDeclaration<T> result =
        FunctionDeclarationImpl.of(
            pName,
            FunctionDeclarationKind.UF,
            pArgTypes,
            pReturnType,
            formulaCreator.declareUFImpl(pName, toSolverType(pReturnType), argTypes));
    if (Generator.isLoggingEnabled()) {
      UFGenerator.logMakeFun(result, pName, pReturnType, pArgTypes);
    }
    return result;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {
    checkVariableName(pName);
    return declareUF(pName, pReturnType, Arrays.asList(pArgs));
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    T result = formulaCreator.callFunction(funcType, Arrays.asList(args));
    if (Generator.isLoggingEnabled()) {
      UFGenerator.logCallFun(result, funcType, args);
    }
    return result;
  }

  @Override
  public final <T extends Formula> T callUF(
      FunctionDeclaration<T> pFunc, List<? extends Formula> pArgs) {
    T result = formulaCreator.callFunction(pFunc, pArgs);
    if (Generator.isLoggingEnabled()) {
      UFGenerator.logCallFun(result, pFunc, pArgs);
    }
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    checkVariableName(name);
    if (Generator.isLoggingEnabled()) {
      // FIXME Find a better way to handle quoted symbols
      if (name.contains("PIPE")) {
        name = name.replaceAll("PIPE", "|");
      }
    }
    List<FormulaType<?>> argTypes = Lists.transform(pArgs, getFormulaCreator()::getFormulaType);
    FunctionDeclaration<T> func = declareUF(name, pReturnType, argTypes);
    T result = callUF(func, pArgs);
    if (Generator.isLoggingEnabled()) {
      UFGenerator.logCallFun(result, declareUF(name, pReturnType, argTypes), pArgs);
    }
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    checkVariableName(name);
    return declareAndCallUF(name, pReturnType, Arrays.asList(pArgs));
  }
}
