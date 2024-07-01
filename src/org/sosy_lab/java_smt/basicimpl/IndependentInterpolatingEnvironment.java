/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;

public abstract class IndependentInterpolatingEnvironment<Formula>
        implements InterpolatingProverEnvironment<Formula> {

    private final FormulaManager mgr;

    protected IndependentInterpolatingEnvironment(FormulaManager pMgr) {
        mgr = pMgr;
    }

    public void interpolate(BooleanFormula A, BooleanFormula B) {

    }

}
