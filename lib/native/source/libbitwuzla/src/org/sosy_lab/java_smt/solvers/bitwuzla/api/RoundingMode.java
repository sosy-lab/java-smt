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

public final class RoundingMode {
  public final static RoundingMode RNE = new RoundingMode("RNE", BitwuzlaNativeJNI.RoundingMode_RNE_get());
  public final static RoundingMode RNA = new RoundingMode("RNA", BitwuzlaNativeJNI.RoundingMode_RNA_get());
  public final static RoundingMode RTN = new RoundingMode("RTN", BitwuzlaNativeJNI.RoundingMode_RTN_get());
  public final static RoundingMode RTP = new RoundingMode("RTP", BitwuzlaNativeJNI.RoundingMode_RTP_get());
  public final static RoundingMode RTZ = new RoundingMode("RTZ", BitwuzlaNativeJNI.RoundingMode_RTZ_get());

  public final int swigValue() {
    return swigValue;
  }

  public String toString() {
    return swigName;
  }

  public static RoundingMode swigToEnum(int swigValue) {
    if (swigValue < swigValues.length && swigValue >= 0 && swigValues[swigValue].swigValue == swigValue)
      return swigValues[swigValue];
    for (int i = 0; i < swigValues.length; i++)
      if (swigValues[i].swigValue == swigValue)
        return swigValues[i];
    throw new IllegalArgumentException("No enum " + RoundingMode.class + " with value " + swigValue);
  }

  private RoundingMode(String swigName) {
    this.swigName = swigName;
    this.swigValue = swigNext++;
  }

  private RoundingMode(String swigName, int swigValue) {
    this.swigName = swigName;
    this.swigValue = swigValue;
    swigNext = swigValue+1;
  }

  private RoundingMode(String swigName, RoundingMode swigEnum) {
    this.swigName = swigName;
    this.swigValue = swigEnum.swigValue;
    swigNext = this.swigValue+1;
  }

  private static RoundingMode[] swigValues = { RNE, RNA, RTN, RTP, RTZ };
  private static int swigNext = 0;
  private final int swigValue;
  private final String swigName;
}

