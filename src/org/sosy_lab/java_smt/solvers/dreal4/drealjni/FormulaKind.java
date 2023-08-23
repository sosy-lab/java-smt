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

public final class FormulaKind {
  public static final FormulaKind.FormulaType FALSE = new FormulaKind.FormulaType("False");
  public static final FormulaKind.FormulaType TRUE = new FormulaKind.FormulaType("True");
  public static final FormulaKind.FormulaType VAR = new FormulaKind.FormulaType("Var");
  public static final FormulaKind.FormulaType EQ = new FormulaKind.FormulaType("Eq");
  public static final FormulaKind.FormulaType NEQ = new FormulaKind.FormulaType("Neq");
  public static final FormulaKind.FormulaType GT = new FormulaKind.FormulaType("Gt");
  public static final FormulaKind.FormulaType GEQ = new FormulaKind.FormulaType("Geq");
  public static final FormulaKind.FormulaType LT = new FormulaKind.FormulaType("Lt");
  public static final FormulaKind.FormulaType LEQ = new FormulaKind.FormulaType("Leq");
  public static final FormulaKind.FormulaType AND = new FormulaKind.FormulaType("And");
  public static final FormulaKind.FormulaType OR = new FormulaKind.FormulaType("Or");
  public static final FormulaKind.FormulaType NOT = new FormulaKind.FormulaType("Not");
  public static final FormulaKind.FormulaType FORALL = new FormulaKind.FormulaType("Forall");
  private static FormulaKind.FormulaType[] swigValues = {
    FALSE, TRUE, VAR, EQ, NEQ, GT, GEQ, LT, LEQ, AND, OR, NOT, FORALL,
  };
  private static int swigNext = 0;

  public static FormulaKind.FormulaType swigToEnum(int swigValue) {
    if (swigValue < swigValues.length
        && swigValue >= 0
        && swigValues[swigValue].swigValue() == swigValue) {
      return swigValues[swigValue];
    }
    for (int i = 0; i < swigValues.length; i++) {
      {
        if (swigValues[i].swigValue() == swigValue) {
          return swigValues[i];
        }
      }
    }
    throw new IllegalArgumentException(
        "No enum " + FormulaKind.FormulaType.class + " with value " + swigValue);
  }

  public static class FormulaType {
    private final int swigValue;
    private final String swigName;

    public FormulaType(String swigName) {
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
