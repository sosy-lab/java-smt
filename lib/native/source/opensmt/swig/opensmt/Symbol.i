// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore SymbolProperty;
%ignore SymbolConfig;
%ignore SymConf;
%ignore SymbolMatcher;

//%ignore Symbol;
//%ignore Symbol::size ();
%ignore Symbol::operator[] (int i) const;
%ignore Symbol::begin () const;
%ignore Symbol::end () const;
//%ignore Symbol::rsort () const;
%ignore Symbol::commutes () const;
%ignore Symbol::relocation () const;
%ignore Symbol::type () const;
%ignore Symbol::left_assoc () const;
%ignore Symbol::right_assoc () const;
%ignore Symbol::chainable () const;
%ignore Symbol::pairwise () const;
%ignore Symbol::noScoping () const;
//%ignore Symbol::nargs () const;
%ignore Symbol::getId () const;
%ignore Symbol::setId (int i);
//%ignore Symbol::isInterpreted () const;
%ignore Symbol::matches (SymbolMatcher matcher) const;
%extend Symbol {
  %newobject getArgs;
  std::vector<SRef> getArgs() {
    std::vector<SRef> args;
    for(auto i=0; i<$self->nargs(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }
 }

%ignore SymbolAllocator;

%include "include/opensmt/Symbol.h"
