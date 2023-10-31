// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore FunctionSignature;

%ignore TemplateFunction::TemplateFunction ();
%ignore TemplateFunction::TemplateFunction (const std::string &name, const vec< PTRef > &args_, SRef ret_sort, PTRef tr_body);
%ignore TemplateFunction::TemplateFunction (FunctionSignature &&signature, PTRef body);
%ignore TemplateFunction::TemplateFunction (const TemplateFunction &other);
%ignore TemplateFunction::TemplateFunction (TemplateFunction &&other);
%extend TemplateFunction {
  TemplateFunction(const std::string &name, const std::vector< PTRef > &args_, SRef ret_sort, PTRef tr_body) {
    return new TemplateFunction(name, vec(args_), ret_sort, tr_body);
  }
 }
%ignore TemplateFunction::operator= (TemplateFunction &&);
%ignore TemplateFunction::nextFreeArgumentName ();
%ignore TemplateFunction::getArgs () const;
%extend TemplateFunction {
  %newobject getArgs;
  std::vector<PTRef> getArgs() {
    std::vector<PTRef> res;
    for(PTRef a : $self->getArgs()) {
      res.emplace_back(a);
    }
    return res;
  }
}
%ignore TemplateFunction::updateBody (PTRef new_body);

%include "include/opensmt/FunctionTools.h"
