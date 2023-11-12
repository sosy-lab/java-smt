// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore Model::Model (Logic &logic, Evaluation basicEval, SymbolDefinition symbolDef);
%ignore Model::Model (Logic &logic, Evaluation basicEval);

//%ignore Model::getDefinition (SymRef) const;
%ignore Model::getFormalArgBaseNameForSymbol (const Logic &logic, SymRef sr, const std::string &formalArgDefaultPrefix);

%include "include/opensmt/Model.h"
