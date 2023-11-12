// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

/**
 * This file provides the SWIG definition for generating Java code and native bindings for the
 * OpenSMT API.
 *
 * This SWIG definition file only provide the required methods, i.e., a manually selected subset
 * of the full OpenSMT API, to minimize the interaction layer. If further methods are required, we
 * can extend this file. Several utility methods help to avoid low-level C/C++ structures from
 * Java code.
 *
 * See {build/build-publish-solver.xml} for the SWIG command and further steps towards getting a
 * static library of OpenSMT.
 */

%module OsmtNative
%{
#include "Version.h"
#include "include/opensmt/Opensmt.h"
%}

%include <stdint.i>

%include <std_string.i>
%include <std_vector.i>

%template(VectorInt)       std::vector<int>;
%template(VectorPTRef)     std::vector<PTRef>;
%template(VectorSRef)      std::vector<SRef>;
%template(VectorSymRef)    std::vector<SymRef>;
%template(VectorVectorInt) std::vector<std::vector<int>>;

%include <std_unique_ptr.i>

%unique_ptr(Model);
%unique_ptr(InterpolationContext);

%exception {
  try { $action }
  catch(std::exception& e) {
    jclass exceptionType = jenv->FindClass("java/lang/UnsupportedOperationException");
    jenv->ThrowNew(exceptionType, e.what());
    return $null;
  }
  catch(OutOfMemoryException& e) {
    jclass exceptionType = jenv->FindClass("java/lang/OutOfMemoryError");
    jenv->ThrowNew(exceptionType, "");
    return $null;
  }
  catch(...) {
    jclass exceptionType = jenv->FindClass("java/lang/RuntimeException");
    jenv->ThrowNew(exceptionType, "");
    return $null;
  }
}

%include "swig/opensmt/Logic.i"
%include "swig/opensmt/ArithLogic.i"
%include "swig/opensmt/FunctionTools.i"
%include "swig/opensmt/InterpolationContext.i"
%include "swig/opensmt/LogicFactory.i"
%include "swig/opensmt/MainSolver.i"
%include "swig/opensmt/Model.i"
%include "swig/opensmt/Pterm.i"
%include "swig/opensmt/PTRef.i"
%include "swig/opensmt/SMTConfig.i"
%include "swig/opensmt/SSort.i"
%include "swig/opensmt/Symbol.i"
%include "swig/opensmt/SymRef.i"
