// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.util.Objects;

// Declarations sometimes need the info of a Term, but mostly those of Kinds.
// We can not discern between the two however, hence this wrapper
public class BitwuzlaDeclaration {
  private final Long decl;

  // If isKind, decl == KIND; else decl == term
  private final boolean isKind;

  BitwuzlaDeclaration(long pDecl, boolean pIsKind) {
    decl = pDecl;
    isKind = pIsKind;
  }

  public boolean isKind() {
    return isKind;
  }

  public long getTerm() {
    assert !isKind;
    return decl;
  }

  public int getKind() {
    assert isKind;
    return decl.intValue();
  }

  @Override
  public boolean equals(Object any) {
    if (any == this) {
      return true;
    }
    if (any instanceof BitwuzlaDeclaration) {
      BitwuzlaDeclaration otherDecl = (BitwuzlaDeclaration) any;
      if (this.isKind == otherDecl.isKind && Objects.equals(this.decl, otherDecl.decl)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public int hashCode() {
    // Might be errorprone as term and kind might have the same hashcode but not be equal
    return decl != null ? decl.hashCode() : 0;
  }
}
