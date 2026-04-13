// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.collect.ImmutableList;
import java.util.Objects;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

final class LeanSmtFunctionDecl {

  private final String name;
  private final FunctionDeclarationKind kind;
  private final LeanSmtType returnType;
  private final ImmutableList<LeanSmtType> argumentTypes;

  LeanSmtFunctionDecl(
      String pName,
      FunctionDeclarationKind pKind,
      LeanSmtType pReturnType,
      ImmutableList<LeanSmtType> pArgTypes) {
    name = pName;
    kind = pKind;
    returnType = pReturnType;
    argumentTypes = pArgTypes;
  }

  LeanSmtFunctionDecl(String pName, LeanSmtType pReturnType, ImmutableList<LeanSmtType> pArgTypes) {
    this(pName, FunctionDeclarationKind.UF, pReturnType, pArgTypes);
  }

  String getName() {
    return name;
  }

  FunctionDeclarationKind getKind() {
    return kind;
  }

  LeanSmtType getReturnType() {
    return returnType;
  }

  ImmutableList<LeanSmtType> getArgumentTypes() {
    return argumentTypes;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (!(other instanceof LeanSmtFunctionDecl)) {
      return false;
    }
    LeanSmtFunctionDecl that = (LeanSmtFunctionDecl) other;
    return name.equals(that.name)
        && kind == that.kind
        && returnType.equals(that.returnType)
        && argumentTypes.equals(that.argumentTypes);
  }

  @Override
  public int hashCode() {
    return Objects.hash(name, kind, returnType, argumentTypes);
  }
}
