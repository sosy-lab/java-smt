// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.auto.value.AutoValue;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;

// Declarations sometimes need the info of a Term, but mostly those of Kinds.
// We can not discern between the two however, hence this wrapper
@AutoValue
public abstract class BitwuzlaDeclaration {
  public abstract @Nullable Term getTerm();

  public abstract @Nullable Kind getKind();

  public static BitwuzlaDeclaration create(Term pTerm) {
    return new AutoValue_BitwuzlaDeclaration(pTerm, null);
  }

  public static BitwuzlaDeclaration create(Kind pKind) {
    return new AutoValue_BitwuzlaDeclaration(null, pKind);
  }

  public boolean isTerm() {
    return getTerm() != null;
  }

  public boolean isKind() {
    return getKind() != null;
  }
}
