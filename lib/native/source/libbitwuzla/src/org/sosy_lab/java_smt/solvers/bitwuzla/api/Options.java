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

public class Options {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected Options(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Options obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(Options obj) {
    long ptr = 0;
    if (obj != null) {
      if (!obj.swigCMemOwn)
        throw new RuntimeException("Cannot release ownership as memory is not owned");
      ptr = obj.swigCPtr;
      obj.swigCMemOwn = false;
      obj.delete();
    }
    return ptr;
  }

  @SuppressWarnings("deprecation")
  protected void finalize() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        BitwuzlaNativeJNI.delete_Options(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Options() {
    this(BitwuzlaNativeJNI.new_Options__SWIG_0(), true);
  }

  public Options(Options options) {
    this(BitwuzlaNativeJNI.new_Options__SWIG_1(Options.getCPtr(options), options), true);
  }

  public boolean is_valid(String name) {
    return BitwuzlaNativeJNI.Options_is_valid(swigCPtr, this, name);
  }

  public boolean is_bool(Option option) {
    return BitwuzlaNativeJNI.Options_is_bool(swigCPtr, this, option.swigValue());
  }

  public boolean is_numeric(Option option) {
    return BitwuzlaNativeJNI.Options_is_numeric(swigCPtr, this, option.swigValue());
  }

  public boolean is_mode(Option option) {
    return BitwuzlaNativeJNI.Options_is_mode(swigCPtr, this, option.swigValue());
  }

  public String shrt(Option option) {
    return BitwuzlaNativeJNI.Options_shrt(swigCPtr, this, option.swigValue());
  }

  public String lng(Option option) {
    return BitwuzlaNativeJNI.Options_lng(swigCPtr, this, option.swigValue());
  }

  public String description(Option option) {
    return BitwuzlaNativeJNI.Options_description(swigCPtr, this, option.swigValue());
  }

  public Vector_String modes(Option option) {
    return new Vector_String(BitwuzlaNativeJNI.Options_modes(swigCPtr, this, option.swigValue()), true);
  }

  public Option option(String name) {
    return Option.swigToEnum(BitwuzlaNativeJNI.Options_option(swigCPtr, this, name));
  }

  public void set(Option option, String mode) {
    BitwuzlaNativeJNI.Options_set__SWIG_0(swigCPtr, this, option.swigValue(), mode);
  }

  public void set(String lng, String value) {
    BitwuzlaNativeJNI.Options_set__SWIG_1(swigCPtr, this, lng, value);
  }

  public void set(Vector_String args) {
    BitwuzlaNativeJNI.Options_set__SWIG_2(swigCPtr, this, Vector_String.getCPtr(args), args);
  }

  public java.math.BigInteger get(Option option) {
    return BitwuzlaNativeJNI.Options_get(swigCPtr, this, option.swigValue());
  }

  public String get_mode(Option option) {
    return BitwuzlaNativeJNI.Options_get_mode(swigCPtr, this, option.swigValue());
  }

  public void set(Option option, int value) {
    BitwuzlaNativeJNI.Options_set__SWIG_3(swigCPtr, this, option.swigValue(), value);
  }

}
