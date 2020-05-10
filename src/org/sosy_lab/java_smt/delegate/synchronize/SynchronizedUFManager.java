/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.UFManager;

class SynchronizedUFManager implements UFManager {

  private final UFManager delegate;
  private final SolverContext sync;

  SynchronizedUFManager(UFManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgs) {
    synchronized (sync) {
      return delegate.declareUF(pName, pReturnType, pArgs);
    }
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {
    synchronized (sync) {
      return delegate.declareUF(pName, pReturnType, pArgs);
    }
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> pFuncType, List<? extends Formula> pArgs) {
    synchronized (sync) {
      return delegate.callUF(pFuncType, pArgs);
    }
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> pFuncType, Formula... pArgs) {
    synchronized (sync) {
      return delegate.callUF(pFuncType, pArgs);
    }
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String pName, FormulaType<T> pReturnType, List<Formula> pArgs) {
    synchronized (sync) {
      return delegate.declareAndCallUF(pName, pReturnType, pArgs);
    }
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String pName, FormulaType<T> pReturnType, Formula... pArgs) {
    synchronized (sync) {
      return delegate.declareAndCallUF(pName, pReturnType, pArgs);
    }
  }
}
