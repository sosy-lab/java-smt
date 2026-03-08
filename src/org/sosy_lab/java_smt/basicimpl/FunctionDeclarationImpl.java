// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.Immutable;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

/** Declaration of a function. */
@Immutable(containerOf = "T")
public record FunctionDeclarationImpl<F extends Formula, T>(
    FunctionDeclarationKind getKind,
    String getName,
    FormulaType<F> getType,
    ImmutableList<FormulaType<?>> getArgumentTypes,
    T getSolverDeclaration)
    implements FunctionDeclaration<F> {

  public static <F extends Formula, T> FunctionDeclarationImpl<F, T> of(
      String name,
      FunctionDeclarationKind kind,
      List<FormulaType<?>> pArgumentTypes,
      FormulaType<F> pReturnType,
      T pDeclaration) {
    return new FunctionDeclarationImpl<>(
        kind, name, pReturnType, ImmutableList.copyOf(pArgumentTypes), pDeclaration);
  }

  @Override
  public String toString() {
    return "%s (%s)".formatted(getKind(), getName());
  }
}
