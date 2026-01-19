// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;

public class DebuggingUFManager implements UFManager {
  private final UFManager delegate;
  private final DebuggingAssertions debugging;

  DebuggingUFManager(UFManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    debugging.assertThreadLocal();
    FunctionDeclaration<T> result = delegate.declareUF(name, returnType, args);
    debugging.addFunctionDeclaration(result);
    return result;
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    debugging.assertThreadLocal();
    debugging.assertDeclarationInContext(funcType);
    for (Formula t : args) {
      debugging.assertFormulaInContext(t);
    }
    T result = delegate.callUF(funcType, args);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    debugging.assertThreadLocal();
    for (Formula t : pArgs) {
      debugging.assertFormulaInContext(t);
    }
    T result = delegate.declareAndCallUF(name, pReturnType, pArgs);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    debugging.assertThreadLocal();
    for (Formula t : pArgs) {
      debugging.assertFormulaInContext(t);
    }
    T result = delegate.declareAndCallUF(name, pReturnType, pArgs);
    debugging.addFormulaTerm(result);
    return result;
  }
}
