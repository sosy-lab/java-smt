// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//%ignore SSymRef;
%ignore SSymRef::operator= (uint32_t v);
%ignore operator== (SSymRef a1, SSymRef a2);
%ignore operator!= (SSymRef a1, SSymRef a2);

%ignore SSymRef_Undef;
%ignore SSymRefHash;

%typemap(javacode) SSymRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SSymRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }

  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

//%ignore SortSymbol;
%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity);
%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity, unsigned int flags);
%ignore SortSymbol::SortSymbol (SortSymbol &&);
%ignore SortSymbol::SortSymbol (SortSymbol const &);
//%ignore SortSymbol::isInternal () const;
//%ignore SortSymbol::name;
//%ignore SortSymbol::arity;
%ignore SortSymbol::flags;

//$ignore SRef;
%ignore SRef::operator= (uint32_t v);
%ignore operator== (SRef a1, SRef a2);
%ignore operator!= (SRef a1, SRef a2);

%ignore SRef_Undef;
%ignore SRef_Nil;

%ignore SRefHash;

%typemap(javacode) SRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }

  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

//%ignore Sort;
%ignore Sort::Sort (SSymRef symRef_, sortid_t uniq_id_, vec< SRef > const &rest);
%ignore Sort::getId () const;
//%ignore Sort::getSymRef () const;
//%ignore Sort::getSize () const;
%ignore Sort::operator[] (uint32_t index) const;
%extend Sort {
  %newobject getArgs;
  std::vector<SRef> getArgs() {
    std::vector<SRef> args;
    for(auto i=0; i<$self->getSize(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }
 }

%ignore SortKey;
%ignore SortSymbolAllocator;

%ignore SortAllocator;

%include "include/opensmt/SSort.h"
