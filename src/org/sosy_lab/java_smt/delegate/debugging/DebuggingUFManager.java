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
import org.sosy_lab.java_smt.delegate.debugging.DebuggingSolverContext.NodeManager;

public class DebuggingUFManager extends FormulaChecks implements UFManager {
  private final UFManager delegate;

  public DebuggingUFManager(UFManager pDelegate, NodeManager pLocalFormulas) {
    super(pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    // TODO: FunctionDeclarations and FormulaTypes should probably be tracked too?
    assertThreadLocal();
    return delegate.declareUF(name, returnType, args);
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, FormulaType<?>... args) {
    assertThreadLocal();
    return delegate.declareUF(name, returnType, args);
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    assertThreadLocal();
    for (Formula t : args) {
      assertFormulaInContext(t);
    }
    T result = delegate.callUF(funcType, args);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    assertThreadLocal();
    for (Formula t : args) {
      assertFormulaInContext(t);
    }
    T result = delegate.callUF(funcType, args);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    assertThreadLocal();
    for (Formula t : pArgs) {
      assertFormulaInContext(t);
    }
    T result = delegate.declareAndCallUF(name, pReturnType, pArgs);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    assertThreadLocal();
    for (Formula t : pArgs) {
      assertFormulaInContext(t);
    }
    T result = delegate.declareAndCallUF(name, pReturnType, pArgs);
    addFormulaToContext(result);
    return result;
  }
}
