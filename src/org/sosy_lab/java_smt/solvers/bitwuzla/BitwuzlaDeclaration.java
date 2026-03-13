// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;

// Declarations sometimes need the info of a Term, but mostly those of Kinds.
// We can not discern between the two however, hence this wrapper
public record BitwuzlaDeclaration(@Nullable Term getTerm, @Nullable Kind getKind) {

  public BitwuzlaDeclaration {
    checkArgument(
        (getTerm == null) != (getKind == null), "Exactly one of term and kind must be non-null");
  }

  public static BitwuzlaDeclaration create(Term pTerm) {
    return new BitwuzlaDeclaration(pTerm, null);
  }

  public static BitwuzlaDeclaration create(Kind pKind) {
    return new BitwuzlaDeclaration(null, pKind);
  }

  public boolean isTerm() {
    return getTerm != null;
  }

  public boolean isKind() {
    return getKind != null;
  }
}
