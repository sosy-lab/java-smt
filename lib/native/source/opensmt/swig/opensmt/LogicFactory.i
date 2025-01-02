// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {
%ignore Arithmetic_t;

%ignore ArithProperty;
%ignore no_arith;

%ignore UFProperty;
%ignore no_uf;

%ignore BVProperty;
%ignore no_bv;

%ignore LogicProperty;

%ignore QFLogicToProperties;
%ignore getLogicFromString(const std::string & name);
%ignore getStringFromLogic(const Logic_t logic);

%ignore LogicFactory::LogicFactory();

%newobject LogicFactory::getInstance(Logic_t);
%newobject LogicFactory::getLAInstance(Logic_t);
%newobject LogicFactory::getLRAInstance();
%newobject LogicFactory::getLIAInstance();

%extend LogicFactory {
  static std::string getVersion() {
    return std::string(VERSION);
  }
 }
}

%include "include/opensmt/logics/LogicFactory.h"
