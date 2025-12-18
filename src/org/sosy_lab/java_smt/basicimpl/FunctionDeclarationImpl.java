// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.auto.value.AutoValue;
import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.Immutable;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

/** Declaration of a function. */
@Immutable(containerOf = "T")
@AutoValue
public abstract class FunctionDeclarationImpl<F extends Formula, T>
    implements FunctionDeclaration<F> {

  public static <F extends Formula, T> FunctionDeclaration<F> of(
      String name,
      FunctionDeclarationKind kind,
      List<Integer> pIndices,
      List<FormulaType<?>> pArgumentTypes,
      FormulaType<F> pReturnType,
      T pDeclaration) {
    return new AutoValue_FunctionDeclarationImpl<>(
        kind,
        name,
        ImmutableList.copyOf(pIndices),
        pReturnType,
        ImmutableList.copyOf(pArgumentTypes),
        pDeclaration);
  }

  public static <F extends Formula, T> FunctionDeclaration<F> of(
      String name,
      FunctionDeclarationKind kind,
      List<FormulaType<?>> pArgumentTypes,
      FormulaType<F> pReturnType,
      T pDeclaration) {
    return of(name, kind, ImmutableList.of(), pArgumentTypes, pReturnType, pDeclaration);
  }

  /**
   * get a reference to the internal declaration used by the SMT solver. This method should only be
   * used internally in JavaSMT.
   */
  public abstract T getSolverDeclaration();

  @Override
  public final String toString() {
    return String.format("%s (%s)", getKind(), getName());
  }
}
