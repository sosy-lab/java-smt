// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.Immutable;
import java.util.List;
import java.util.Objects;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

/** Declaration of a function. */
@Immutable(containerOf = "T")
public final class FunctionDeclarationImpl<F extends Formula, T> implements FunctionDeclaration<F> {
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
