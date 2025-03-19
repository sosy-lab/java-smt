// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {
%ignore SSymRef::SSymRef();
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

%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity);
%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity, unsigned int flags);
%ignore SortSymbol::SortSymbol (SortSymbol &&);
%ignore SortSymbol::SortSymbol (SortSymbol const &);
%ignore SortSymbol::INTERNAL;
%ignore SortSymbol::arity;
%extend SortSymbol {
  unsigned int getArity() {
    return $self->arity;
  }
 }
%ignore SortSymbol::name;
%extend SortSymbol {
  std::string getName() {
    return $self->name;
  }
 }
%ignore SortSymbol::flags;

%ignore SRef::SRef();
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

%ignore Sort::Sort (SSymRef symRef_, sortid_t uniq_id_, vec< SRef > const &rest);
%ignore Sort::getId () const;
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
}

%include "include/opensmt/sorts/SSort.h"
