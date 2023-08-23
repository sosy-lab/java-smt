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

public final class Logic {
  public static final Logic.LogicType ALL = new Logic.LogicType("ALL");
  public static final Logic.LogicType QF_LIA = new Logic.LogicType("QF_LIA");
  public static final Logic.LogicType QF_LIRA = new Logic.LogicType("QF_LIRA");
  public static final Logic.LogicType QF_LRA = new Logic.LogicType("QF_LRA");
  public static final Logic.LogicType QF_NIA = new Logic.LogicType("QF_NIA");
  public static final Logic.LogicType QF_NIAT = new Logic.LogicType("QF_NIAT");
  public static final Logic.LogicType QF_NIRA = new Logic.LogicType("QF_NIRA");
  public static final Logic.LogicType QF_NIRAT = new Logic.LogicType("QF_NIRAT");
  public static final Logic.LogicType QF_NRA = new Logic.LogicType("QF_NRA");
  public static final Logic.LogicType QF_NRAT = new Logic.LogicType("QF_NRAT");
  public static final Logic.LogicType QF_RDL = new Logic.LogicType("QF_RDL");
  private static Logic.LogicType[] swigValues = {
      ALL, QF_LIA, QF_LIRA, QF_LRA, QF_NIA, QF_NIAT, QF_NIRA, QF_NIRAT, QF_NRA, QF_NRAT, QF_RDL,
  };
  private static int swigNext = 0;

  public static Logic.LogicType swigToEnum(int swigValue) {
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
    throw new IllegalArgumentException("No enum " + Logic.LogicType.class + " with value " + swigValue);
  }


  public static class LogicType {
    private final int swigValue;
    private final String swigName;
    public LogicType(String swigName) {
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

