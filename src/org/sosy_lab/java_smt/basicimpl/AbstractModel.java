// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Joiner;
import org.sosy_lab.java_smt.api.Model;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractModel<TFormulaInfo, TType, TEnv>
    extends AbstractEvaluator<TFormulaInfo, TType, TEnv> implements Model {

  protected AbstractModel(
      AbstractProver<?> prover,
      AbstractFormulaManager<TFormulaInfo, TType, TEnv, ?> pFormulaManager) {
    super(prover, pFormulaManager);
  }

  @Override
  public String toString() {
    return Joiner.on('\n').join(iterator());
  }
}