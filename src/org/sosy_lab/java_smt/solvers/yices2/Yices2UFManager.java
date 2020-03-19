/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  SPDX-License-Identifier: Apache-2.0 AND GPL-3.0-or-later
 */
package org.sosy_lab.java_smt.solvers.yices2;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class Yices2UFManager extends AbstractUFManager<Integer, Integer, Integer, Long> {

  protected Yices2UFManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
  }
}
