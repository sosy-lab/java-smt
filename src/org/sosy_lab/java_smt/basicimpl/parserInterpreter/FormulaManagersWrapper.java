// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;

/**
 * This class is a wrapper for the FormulaManager class. It is used to store the different formula
 * managers in a single object. It is used in order to prevent too many arguments in the
 * Constructors
 */
public class FormulaManagersWrapper {
  private FormulaManager fmgr;
  private BooleanFormulaManager bmgr;
  @Nullable private IntegerFormulaManager imgr;
  @Nullable private RationalFormulaManager rmgr;
  @Nullable private BitvectorFormulaManager bimgr;
  @Nullable private ArrayFormulaManager amgr;
  private UFManager umgr;
  @Nullable private FloatingPointFormulaManager fpmgr;
  @Nullable private StringFormulaManager smgr;

  public FormulaManagersWrapper(FormulaManager pFmgr) {
    fmgr = pFmgr;
    bmgr = pFmgr.getBooleanFormulaManager();
    try {
      imgr = pFmgr.getIntegerFormulaManager();
    } catch (UnsupportedOperationException e) {
      imgr = null;
    }
    try {
      rmgr = pFmgr.getRationalFormulaManager();
    } catch (UnsupportedOperationException e) {
      rmgr = null;
    }
    try {
      bimgr = pFmgr.getBitvectorFormulaManager();
    } catch (UnsupportedOperationException e) {
      bimgr = null;
    }
    try {
      amgr = pFmgr.getArrayFormulaManager();
    } catch (UnsupportedOperationException e) {
      amgr = null;
    }
    try {
      fpmgr = pFmgr.getFloatingPointFormulaManager();
    } catch (UnsupportedOperationException e) {
      fpmgr = null;
    }
    try {
      smgr = pFmgr.getStringFormulaManager();
    } catch (UnsupportedOperationException e) {
      smgr = null;
    }
    umgr = pFmgr.getUFManager();
  }

  public FormulaManager getFmgr() {
    return fmgr;
  }

  public BooleanFormulaManager getBmgr() {
    return bmgr;
  }

  public @Nullable IntegerFormulaManager getImgr() {
    return imgr;
  }

  public @Nullable RationalFormulaManager getRmgr() {
    return rmgr;
  }

  public @Nullable BitvectorFormulaManager getBimgr() {
    return bimgr;
  }

  public @Nullable ArrayFormulaManager getAmgr() {
    return amgr;
  }

  public UFManager getUmgr() {
    return umgr;
  }

  public @Nullable FloatingPointFormulaManager getFpmgr() {
    return fpmgr;
  }

  public @Nullable StringFormulaManager getSmgr() {
    return smgr;
  }
}
