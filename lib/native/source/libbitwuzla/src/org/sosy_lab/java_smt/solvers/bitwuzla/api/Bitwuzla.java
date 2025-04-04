// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.sosy_lab.java_smt.solvers.bitwuzla.api;

public class Bitwuzla {
  private transient long swigCPtr;
  private transient boolean swigCMemOwn;

  protected Bitwuzla(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Bitwuzla obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected void swigSetCMemOwn(boolean own) {
    swigCMemOwn = own;
  }

  @SuppressWarnings("deprecation")
  protected void finalize() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        BitwuzlaNativeJNI.delete_Bitwuzla(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Bitwuzla(TermManager tm, Options options) {
    this(BitwuzlaNativeJNI.new_Bitwuzla__SWIG_0(TermManager.getCPtr(tm), tm, Options.getCPtr(options), options), true);
  }

  public Bitwuzla(TermManager tm) {
    this(BitwuzlaNativeJNI.new_Bitwuzla__SWIG_1(TermManager.getCPtr(tm), tm), true);
  }

  public void configure_terminator(Terminator terminator) {
    BitwuzlaNativeJNI.Bitwuzla_configure_terminator(swigCPtr, this, Terminator.getCPtr(terminator), terminator);
  }

  public void push(long nlevels) {
    BitwuzlaNativeJNI.Bitwuzla_push(swigCPtr, this, nlevels);
  }

  public void pop(long nlevels) {
    BitwuzlaNativeJNI.Bitwuzla_pop(swigCPtr, this, nlevels);
  }

  public void assert_formula(Term term) {
    BitwuzlaNativeJNI.Bitwuzla_assert_formula(swigCPtr, this, Term.getCPtr(term), term);
  }

  public Vector_Term get_assertions() {
    return new Vector_Term(BitwuzlaNativeJNI.Bitwuzla_get_assertions(swigCPtr, this), true);
  }

  public Vector_Term get_unsat_assumptions() {
    return new Vector_Term(BitwuzlaNativeJNI.Bitwuzla_get_unsat_assumptions(swigCPtr, this), true);
  }

  public Vector_Term get_unsat_core() {
    return new Vector_Term(BitwuzlaNativeJNI.Bitwuzla_get_unsat_core(swigCPtr, this), true);
  }

  public Term simplify(Term term) {
    return new Term(BitwuzlaNativeJNI.Bitwuzla_simplify(swigCPtr, this, Term.getCPtr(term), term), true);
  }

  public Result check_sat(Vector_Term assumptions) {
    return Result.swigToEnum(BitwuzlaNativeJNI.Bitwuzla_check_sat__SWIG_0(swigCPtr, this, Vector_Term.getCPtr(assumptions), assumptions));
  }

  public Result check_sat() {
    return Result.swigToEnum(BitwuzlaNativeJNI.Bitwuzla_check_sat__SWIG_1(swigCPtr, this));
  }

  public Term get_value(Term term) {
    return new Term(BitwuzlaNativeJNI.Bitwuzla_get_value(swigCPtr, this, Term.getCPtr(term), term), true);
  }

  public TermManager term_mgr() {
    return new TermManager(BitwuzlaNativeJNI.Bitwuzla_term_mgr(swigCPtr, this), false);
  }

  public String print_formula() {
    return BitwuzlaNativeJNI.Bitwuzla_print_formula(swigCPtr, this);
  }

}
