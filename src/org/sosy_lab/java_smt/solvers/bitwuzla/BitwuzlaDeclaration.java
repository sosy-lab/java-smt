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
