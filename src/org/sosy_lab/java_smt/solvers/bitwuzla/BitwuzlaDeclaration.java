// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.util.Objects;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;

// Declarations sometimes need the info of a Term, but mostly those of Kinds.
// We can not discern between the two however, hence this wrapper
public class BitwuzlaDeclaration {
  private final Object decl;

  // If isKind, decl == KIND; else decl == term
  private final boolean isKind;

  BitwuzlaDeclaration(Term pTerm) {
    decl = pTerm;
    isKind = false;
  }

  BitwuzlaDeclaration(Kind pKind) {
    decl = pKind;
    isKind = true;
  }

  public boolean isKind() {
    return isKind;
  }

  public Term getTerm() {
    assert !isKind;
    return (Term) decl;
  }

  public Kind getKind() {
    assert isKind;
    return (Kind) decl;
  }

  @Override
  public boolean equals(Object any) {
    if (any == this) {
      return true;
    }
    if (any instanceof BitwuzlaDeclaration) {
      BitwuzlaDeclaration otherDecl = (BitwuzlaDeclaration) any;
      return isKind == otherDecl.isKind && Objects.equals(decl, otherDecl.decl);
    }
    return false;
  }

  @Override
  public int hashCode() {
    return Objects.hash(decl, isKind);
  }
}
