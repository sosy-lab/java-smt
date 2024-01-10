// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (http://www.swig.org).
 * Version 4.0.2
 *
 * Do not make changes to this file unless you know what you are doing--modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.sosy_lab.java_smt.solvers.bitwuzla;

public class BitwuzlaOptionInfo {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected BitwuzlaOptionInfo(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(BitwuzlaOptionInfo obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        BitwuzlaJNI.delete_BitwuzlaOptionInfo(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public void setOpt(BitwuzlaOption value) {
    BitwuzlaJNI.BitwuzlaOptionInfo_opt_set(swigCPtr, this, value.swigValue());
  }

  public BitwuzlaOption getOpt() {
    return BitwuzlaOption.swigToEnum(BitwuzlaJNI.BitwuzlaOptionInfo_opt_get(swigCPtr, this));
  }

  public void setShrt(String value) {
    BitwuzlaJNI.BitwuzlaOptionInfo_shrt_set(swigCPtr, this, value);
  }

  public String getShrt() {
    return BitwuzlaJNI.BitwuzlaOptionInfo_shrt_get(swigCPtr, this);
  }

  public void setLng(String value) {
    BitwuzlaJNI.BitwuzlaOptionInfo_lng_set(swigCPtr, this, value);
  }

  public String getLng() {
    return BitwuzlaJNI.BitwuzlaOptionInfo_lng_get(swigCPtr, this);
  }

  public void setDescription(String value) {
    BitwuzlaJNI.BitwuzlaOptionInfo_description_set(swigCPtr, this, value);
  }

  public String getDescription() {
    return BitwuzlaJNI.BitwuzlaOptionInfo_description_get(swigCPtr, this);
  }

  public void setNumeric(NumericValue value) {
    BitwuzlaJNI.BitwuzlaOptionInfo_numeric_set(swigCPtr, this, NumericValue.getCPtr(value), value);
  }

  public NumericValue getNumeric() {
    long cPtr = BitwuzlaJNI.BitwuzlaOptionInfo_numeric_get(swigCPtr, this);
    return (cPtr == 0) ? null : new NumericValue(cPtr, false);
  }

  public BitwuzlaOptionInfo() {
    this(BitwuzlaJNI.new_BitwuzlaOptionInfo(), true);
  }
}