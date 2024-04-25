// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore SymRef::SymRef();
%ignore SymRef::operator=(uint32_t v);

%ignore operator== (const SymRef& a1, const SymRef& a2);
%ignore operator!= (const SymRef& a1, const SymRef& a2);

%ignore SymRef_Undef;
%ignore SymRef_Nil;

%ignore SymRefHash;
%ignore Equal;

%typemap(javacode) SymRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SymRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }

  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

%include "include/opensmt/SymRef.h"
