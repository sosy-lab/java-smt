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

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Objects;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

/** Declaration of a function. */
public class FunctionDeclarationImpl<F extends Formula, T> implements FunctionDeclaration<F> {
  private final String name;
  private final FunctionDeclarationKind kind;
  private final ImmutableList<FormulaType<?>> argumentTypes;
  private final FormulaType<F> returnType;
  private final T solverDeclaration;

  private FunctionDeclarationImpl(
      String pName,
      FunctionDeclarationKind pKind,
      List<FormulaType<?>> pArgumentTypes,
      FormulaType<F> pReturnType,
      T pSolverDeclaration) {
    solverDeclaration = Preconditions.checkNotNull(pSolverDeclaration);
    argumentTypes = ImmutableList.copyOf(pArgumentTypes);
    returnType = Preconditions.checkNotNull(pReturnType);
    name = Preconditions.checkNotNull(pName);
    kind = Preconditions.checkNotNull(pKind);
  }

  public static <F extends Formula, T> FunctionDeclaration<F> of(
      String name,
      FunctionDeclarationKind kind,
      List<FormulaType<?>> pArgumentTypes,
      FormulaType<F> pReturnType,
      T pDeclaration) {
    return new FunctionDeclarationImpl<>(name, kind, pArgumentTypes, pReturnType, pDeclaration);
  }

  /** Get type of the declaration. */
  @Override
  public FunctionDeclarationKind getKind() {
    return kind;
  }

  /** @return Solver-specific representation of the function declaration. */
  public T getSolverDeclaration() {
    return solverDeclaration;
  }

  /**
   * Name of the function. For variables and UF's, it's the user-supplied name. For default
   * theories, it is the operator name (e.g. {@code "ITE"} for the if-then-else operator.)
   */
  @Override
  public String getName() {
    return name;
  }

  @Override
  public List<FormulaType<?>> getArgumentTypes() {
    return argumentTypes;
  }

  @Override
  public FormulaType<F> getType() {
    return returnType;
  }

  @Override
  public String toString() {
    return String.format("%s (%s)", kind, name);
  }

  @Override
  public int hashCode() {
    return Objects.hash(kind, name, argumentTypes, returnType);
  }

  @Override
  public boolean equals(@Nullable Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof FunctionDeclarationImpl)) {
      return false;
    }
    FunctionDeclarationImpl<?, ?> other = (FunctionDeclarationImpl<?, ?>) o;
    return name.equals(other.name)
        && kind.equals(other.kind)
        && argumentTypes.equals(other.argumentTypes)
        && returnType.equals(other.returnType);
  }
}
