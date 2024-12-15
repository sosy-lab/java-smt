// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractModel<TFormulaInfo, TType, TEnv>
    extends AbstractEvaluator<TFormulaInfo, TType, TEnv> implements Model {

  protected AbstractModel(
      AbstractProver<?> prover, FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator) {
    super(prover, creator);
  }

  @SuppressWarnings("unchecked")
  private static <E extends Throwable> void sneakyThrow(Throwable e) throws E {
    throw (E) e;
  }

  @Override
  public String toString() {
    try {
      return Joiner.on('\n').join(asList());
    } catch (InterruptedException pE) {
      Thread.currentThread().interrupt();
      sneakyThrow(pE);
    } catch (SolverException pE) {
      sneakyThrow(pE);
    }
    Preconditions.checkState(false, "unreachable code");
    return null;
  }
}
