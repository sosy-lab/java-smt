/**
 * leansmt.i
 *
 * SWIG interface for LeanSMT JNI bindings.
 * Keep this file as the source of truth for regenerating leansmt_wrap.c
 * and LeanSMT*.java JNI binding classes.
 */

%module LeanSMT

%{
#include "leansmt_wrapper.h"
%}

%include "stdint.i"
%include "typemaps.i"

/* Backward-compatible generic constants used by existing Java wrappers. */
%constant int OK = 0;
%constant int ERROR = 1;
%constant int SAT = 0;
%constant int UNSAT = 1;
%constant int UNKNOWN = 2;
%constant int CHECK_ERROR = 3;
%constant int SOLVER_CVC5 = 0;
%constant int SOLVER_Z3 = 1;

/*
 * Free native buffers after creating Java strings for model/proof retrieval.
 * This keeps ownership handling in the generated binding path reproducible.
 */
%typemap(out) char * leansmt_wrapper_get_model, char * leansmt_wrapper_get_value {
  if ($1) {
    $result = (*jenv)->NewStringUTF(jenv, (const char *)$1);
    leansmt_wrapper_free_string($1);
  } else {
    $result = 0;
  }
}

/* Do not expose manual free-string calls to Java.
 * Freeing is handled internally in typemaps above. */
%ignore leansmt_wrapper_free_string;

%include "leansmt_wrapper.h"
