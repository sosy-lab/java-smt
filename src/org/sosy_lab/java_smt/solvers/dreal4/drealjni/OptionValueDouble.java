/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */
package org.sosy_lab.java_smt.solvers.dreal4.drealjni;

public class OptionValueDouble {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected OptionValueDouble(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(OptionValueDouble obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(OptionValueDouble obj) {
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
        drealJNI.delete_OptionValueDouble(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public OptionValueDouble(double value) {
    this(drealJNI.new_OptionValueDouble__SWIG_0(value), true);
  }

  public OptionValueDouble(OptionValueDouble arg0) {
    this(drealJNI.new_OptionValueDouble__SWIG_1(OptionValueDouble.getCPtr(arg0), arg0), true);
  }

  public OptionValueDouble AssignOperator(OptionValueDouble arg0) {
    return new OptionValueDouble(drealJNI.OptionValueDouble_AssignOperator__SWIG_0(swigCPtr, this, OptionValueDouble.getCPtr(arg0), arg0), false);
  }

  public OptionValueDouble AssignOperator(double value) {
    return new OptionValueDouble(drealJNI.OptionValueDouble_AssignOperator__SWIG_2(swigCPtr, this, value), false);
  }

  public OptionValueDouble AssignOperator(SWIGTYPE_p_double value) {
    return new OptionValueDouble(drealJNI.OptionValueDouble_AssignOperator__SWIG_3(swigCPtr, this, SWIGTYPE_p_double.swigRelease(value)), false);
  }

  public double get() {
    return drealJNI.OptionValueDouble_get(swigCPtr, this);
  }

  public void set_from_command_line(double value) {
    drealJNI.OptionValueDouble_set_from_command_line(swigCPtr, this, value);
  }

  public void set_from_file(double value) {
    drealJNI.OptionValueDouble_set_from_file(swigCPtr, this, value);
  }

  public final static class Type {
    public final static OptionValueDouble.Type DEFAULT = new OptionValueDouble.Type("DEFAULT");
    public final static OptionValueDouble.Type FROM_FILE = new OptionValueDouble.Type("FROM_FILE");
    public final static OptionValueDouble.Type FROM_COMMAND_LINE = new OptionValueDouble.Type("FROM_COMMAND_LINE");
    public final static OptionValueDouble.Type FROM_CODE = new OptionValueDouble.Type("FROM_CODE");

    public final int swigValue() {
      return swigValue;
    }

    public String toString() {
      return swigName;
    }

    public static Type swigToEnum(int swigValue) {
      if (swigValue < swigValues.length && swigValue >= 0 && swigValues[swigValue].swigValue == swigValue)
        return swigValues[swigValue];
      for (int i = 0; i < swigValues.length; i++)
        if (swigValues[i].swigValue == swigValue)
          return swigValues[i];
      throw new IllegalArgumentException("No enum " + Type.class + " with value " + swigValue);
    }

    private Type(String swigName) {
      this.swigName = swigName;
      this.swigValue = swigNext++;
    }

    private Type(String swigName, int swigValue) {
      this.swigName = swigName;
      this.swigValue = swigValue;
      swigNext = swigValue+1;
    }

    private Type(String swigName, Type swigEnum) {
      this.swigName = swigName;
      this.swigValue = swigEnum.swigValue;
      swigNext = this.swigValue+1;
    }

    private static Type[] swigValues = { DEFAULT, FROM_FILE, FROM_COMMAND_LINE, FROM_CODE };
    private static int swigNext = 0;
    private final int swigValue;
    private final String swigName;
  }

}