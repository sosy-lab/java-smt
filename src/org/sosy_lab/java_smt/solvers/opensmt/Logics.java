// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

/**
 * OpenSMT requires to set a specific logic upfront. Depending on the logic, the solver can or can
 * not reason about certain formulas.
 *
 * <p>In general, OpenSMT has issues with satisfiability using theory combinations, like Integer and
 * Reals, or interpolation queries involving theory combination and/or Array theory.
 */
public enum Logics {
  CORE, // plain boolean logic

  QF_AX,
  QF_UF,
  QF_IDL,
  QF_RDL,
  QF_LIA,
  QF_LRA,

  QF_ALIA,
  QF_ALRA,

  QF_UFLIA,
  QF_UFLRA,

  QF_AUFLIA,
  QF_AUFLRA,

  QF_AUFLIRA; // includes all logics that OpenSMT supports for now.

  boolean doesLogicSupportArrays() {
    switch (this) {
      case QF_AX:
      case QF_ALIA:
      case QF_ALRA:
      case QF_AUFLIA:
      case QF_AUFLRA:
      case QF_AUFLIRA:
        return true;
      default:
        return false;
    }
  }

  boolean doesLogicSupportUFs() {
    switch (this) {
      case QF_UF:
      case QF_UFLIA:
      case QF_UFLRA:
      case QF_AUFLIA:
      case QF_AUFLRA:
      case QF_AUFLIRA:
        return true;
      default:
        return false;
    }
  }

  boolean doesLogicSupportIntegers() {
    switch (this) {
      case QF_IDL:
      case QF_LIA:
      case QF_ALIA:
      case QF_UFLIA:
      case QF_AUFLIA:
      case QF_AUFLIRA:
        return true;
      default:
        return false;
    }
  }

  boolean doesLogicSupportReals() {
    switch (this) {
      case QF_RDL:
      case QF_LRA:
      case QF_ALRA:
      case QF_UFLRA:
      case QF_AUFLRA:
      case QF_AUFLIRA:
        return true;
      default:
        return false;
    }
  }

  /** OpenSMT only supports interpolation for specific logics, and no logic combinations. */
  boolean doesLogicSupportInterpolation() {
    switch (this) {
      case QF_UF:
      case QF_LIA:
      case QF_LRA:
        return true;
      default:
        return false;
    }
  }
}
