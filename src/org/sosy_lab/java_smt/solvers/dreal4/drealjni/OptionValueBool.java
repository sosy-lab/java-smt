// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */
package org.sosy_lab.java_smt.solvers.dreal4.drealjni;

import javax.annotation.concurrent.NotThreadSafe;

@NotThreadSafe
public class OptionValueBool {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected OptionValueBool(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(OptionValueBool obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(OptionValueBool obj) {
    long ptr = 0;
    if (obj != null) {
      if (!obj.swigCMemOwn) {
        throw new RuntimeException("Cannot release ownership as memory is not owned");
      }
      ptr = obj.swigCPtr;
      obj.swigCMemOwn = false;
      obj.delete();
    }
    return ptr;
  }

  @SuppressWarnings("deprecation")
  protected void finalize1() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        DrealJNI.deleteOptionValueBool(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public OptionValueBool(boolean value) {
    this(DrealJNI.newOptionValueBoolSWIG0(value), true);
  }

  public OptionValueBool(OptionValueBool arg0) {
    this(DrealJNI.newOptionValueBoolSWIG1(OptionValueBool.getCPtr(arg0), arg0), true);
  }

  public OptionValueBool assignOperator(OptionValueBool arg0) {
    return new OptionValueBool(
        DrealJNI.optionValueBoolAssignOperatorSWIG0(
            swigCPtr, this, OptionValueBool.getCPtr(arg0), arg0),
        false);
  }

  public OptionValueBool assignOperator(boolean value) {
    return new OptionValueBool(
        DrealJNI.optionValueBoolAssignOperatorSWIG2(swigCPtr, this, value), false);
  }

  public OptionValueBool assignOperator(SwigTypePBool value) {
    return new OptionValueBool(
        DrealJNI.optionValueBoolAssignOperatorSWIG3(
            swigCPtr, this, SwigTypePBool.swigRelease(value)),
        false);
  }

  public boolean get() {
    return DrealJNI.optionValueBoolGet(swigCPtr, this);
  }

  public void setFromCommandLine(boolean value) {
    DrealJNI.optionValueBoolSetFromCommandLine(swigCPtr, this, value);
  }

  public void setFromFile(boolean value) {
    DrealJNI.optionValueBoolSetFromFile(swigCPtr, this, value);
  }

  public static final class Type {
    public static final OptionValueBool.Type.Kind DEFAULT = new OptionValueBool.Type.Kind("DEFAULT");
    public static final OptionValueBool.Type.Kind FROM_FILE = new OptionValueBool.Type.Kind("FROM_FILE");
    public static final OptionValueBool.Type.Kind FROM_COMMAND_LINE =
        new OptionValueBool.Type.Kind("FROM_COMMAND_LINE");
    public static final OptionValueBool.Type.Kind FROM_CODE = new OptionValueBool.Type.Kind("FROM_CODE");
    private static Type.Kind[] swigValues = {DEFAULT, FROM_FILE, FROM_COMMAND_LINE, FROM_CODE};
    private static int swigNext = 0;

    public static Type.Kind swigToEnum(int swigValue) {
      if (swigValue < swigValues.length
          && swigValue >= 0
          && swigValues[swigValue].swigValue == swigValue) {
        return swigValues[swigValue];
      }
      for (int i = 0; i < swigValues.length; i++) {
        if (swigValues[i].swigValue == swigValue) {
          return swigValues[i];
        }
      }
      throw new IllegalArgumentException("No enum " + Type.class + " with value " + swigValue);
    }
    public static class Kind {
      private final int swigValue;
      private final String swigName;

      public Kind(String swigName) {
        ;
        this.swigName = swigName;
        this.swigValue = swigNext;
        incrementSwigNext();
      }

      private void incrementSwigNext() {
        swigNext++;
      }

      public int swigValue() {
        return this.swigValue;
      }

      @Override
      public String toString() {
        return this.swigName;
      }
    }
  }
}
