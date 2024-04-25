// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore PTRef::PTRef();

%ignore operator==(PTRef, PTRef);
%ignore operator!=(PTRef, PTRef);
%ignore operator>(PTRef, PTRef);
%ignore operator<(PTRef, PTRef);

%ignore PTRef_Undef;
%ignore PTRefHash;
%ignore PTRefPairHash;

%typemap(javacode) PTRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      PTRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }

  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

%include "include/opensmt/PTRef.h"
