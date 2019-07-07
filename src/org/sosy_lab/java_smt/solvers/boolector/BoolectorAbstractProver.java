/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;

abstract class BoolectorAbstractProver<Long> extends AbstractProverWithAllSat<Long> {
  // BoolectorAbstractProver<E, AF> extends AbstractProverWithAllSat<E>
  // AF = assertedFormulas; E = ?

  protected final long btor;
  protected final BoolectorFormulaManager manager;
  private final BoolectorFormulaCreator creator;
  // protected final Deque<List<Long>> assertedFormulas = new ArrayDeque<>(); // all terms on all
  // levels
  // private final Deque<Level> trackingStack = new ArrayDeque<>(); // symbols on all levels
  protected final ShutdownNotifier shutdownNotifier;

  protected boolean wasLastSatCheckSat = false; // and stack is not changed

  // Used/Built by TheoremProver
  protected BoolectorAbstractProver(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator,
      long btor,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pOptions, manager.getBooleanFormulaManager(), pShutdownNotifier);
    this.manager = manager;
    this.creator = creator;
    this.btor = checkNotNull(btor);
    this.shutdownNotifier = checkNotNull(pShutdownNotifier);
  }

  @Override
  public void close() {
    if (!closed) {
      BtorJNI.boolector_delete(btor);
      closed = true;
    }
  }

  /*
   * Boolector should throw its own exceptions that tell you what went wrong!
   */
  @Override
  public boolean isUnsat() throws SolverException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    final int result = (int) BtorJNI.boolector_sat(btor);
    if (BtorSolverResult.swigToEnum(result) == BtorSolverResult.BTOR_RESULT_SAT) {
      wasLastSatCheckSat = true;
      return false;
    } else if (BtorSolverResult.swigToEnum(result) == BtorSolverResult.BTOR_RESULT_UNSAT) {
      return true;
    } else if (BtorSolverResult.swigToEnum(result) == BtorSolverResult.BTOR_RESULT_UNKNOWN) {
      throw new SolverException(
          "Boolector may have ran out of stack or heap memory, try increasing their sizes.");
    } else {
      throw new SolverException("Boolector sat call returned " + result);
    }
  }

}
