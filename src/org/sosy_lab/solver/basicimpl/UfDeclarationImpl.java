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

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.UfDeclaration;

import java.util.List;

import javax.annotation.Nullable;

/**
 * A simple straightforward implementation of {@link UfDeclaration}.
 */
class UfDeclarationImpl<T extends Formula, TFuncDecl>
    extends UfDeclaration<T> {

  private final TFuncDecl funcDecl;

  UfDeclarationImpl(
      FormulaType<T> returnType, TFuncDecl funcDecl, List<FormulaType<?>> argumentTypes) {
    super(returnType, argumentTypes);
    this.funcDecl = checkNotNull(funcDecl);
  }

  TFuncDecl getFuncDecl() {
    return funcDecl;
  }

  @Override
  public int hashCode() {
    return 31 + funcDecl.hashCode();
  }

  @Override
  public boolean equals(@Nullable Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof UfDeclarationImpl)) {
      return false;
    }
    UfDeclarationImpl<?, ?> other =
        (UfDeclarationImpl<?, ?>) obj;

    return funcDecl.equals(other.funcDecl);
  }
}
