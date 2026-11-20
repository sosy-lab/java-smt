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
    return switch (this) {
      case QF_AX, QF_ALIA, QF_ALRA, QF_AUFLIA, QF_AUFLRA, QF_AUFLIRA -> true;
      default -> false;
    };
  }

  boolean doesLogicSupportUFs() {
    return switch (this) {
      case QF_UF, QF_UFLIA, QF_UFLRA, QF_AUFLIA, QF_AUFLRA, QF_AUFLIRA -> true;
      default -> false;
    };
  }

  boolean doesLogicSupportIntegers() {
    return switch (this) {
      case QF_IDL, QF_LIA, QF_ALIA, QF_UFLIA, QF_AUFLIA, QF_AUFLIRA -> true;
      default -> false;
    };
  }

  boolean doesLogicSupportReals() {
    return switch (this) {
      case QF_RDL, QF_LRA, QF_ALRA, QF_UFLRA, QF_AUFLRA, QF_AUFLIRA -> true;
      default -> false;
    };
  }

  /** OpenSMT only supports interpolation for specific logics, and no logic combinations. */
  boolean doesLogicSupportInterpolation() {
    return switch (this) {
      case QF_UF, QF_LIA, QF_LRA -> true;
      default -> false;
    };
  }
}
