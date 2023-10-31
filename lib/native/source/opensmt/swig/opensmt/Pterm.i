// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore PTLKey;
%ignore PTLHash;
%ignore PTId;

%ignore Pterm::operator[] (int i) const;
%ignore Pterm::has_extra () const;
%ignore Pterm::reloced () const;
%ignore Pterm::relocation () const;
%ignore Pterm::relocate (PTRef t);
%ignore Pterm::type () const;
%ignore Pterm::type (uint32_t m);
%ignore Pterm::left_assoc () const;
%ignore Pterm::right_assoc () const;
%ignore Pterm::chainable () const;
%ignore Pterm::pairwise () const;
%ignore Pterm::noScoping () const;
%ignore Pterm::nargs () const;
%ignore Pterm::setLeftAssoc ();
%ignore Pterm::setRightAssoc ();
%ignore Pterm::setChainable ();
%ignore Pterm::setPairwise ();
%ignore Pterm::setNoScoping ();
%ignore Pterm::getId () const;
%ignore Pterm::setId (int i);
%ignore Pterm::shrink (int s);
%ignore Pterm::begin () const;
%ignore Pterm::end () const;
%extend Pterm {
  // FIXME: Causes intermittent crashes in OpenSmtFormulaCreator.visit
  %newobject getArgs;
  std::vector<PTRef> getArgs() {
    std::vector<PTRef> args;
    for(auto i=0; i<$self->size(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }

  PTRef at(int i) {
    return $self->operator[](i);
  }
}

%ignore ptermSort(Pterm&);

%ignore PtPair;
%ignore PtChild;
%ignore PtChildHash;
%ignore PtermAllocator;

%include "include/opensmt/Pterm.h"
