/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import ap.SimpleAPI;
import ap.parser.IFormula;

import org.sosy_lab.solver.SolverException;

import scala.Option;

import java.util.List;
import java.util.Set;

/** This is a Interface for the Wrapper around some parts of the PrincessAPI.
 * It allows to have a stack with operations like:
 * push, pop, assert, checkSat, getInterpolants, getModel.
 * A stack is always connected with a PrincessEnvironment, because Variables are declared there.
 * One PrincessEnvironment can manage several stacks. */
interface PrincessStack {

  void push();

  void pop();

  void assertTerm(IFormula booleanFormula);

  void assertTermInPartition(IFormula booleanFormula, int index);

  boolean checkSat() throws SolverException;

  SimpleAPI.PartialModel getPartialModel();

  Option<Object> evalPartial(IFormula pFormula);

  List<IFormula> getInterpolants(List<Set<Integer>> partitions) throws SolverException;

  /**
   * Clean the stack, such that it can be re-used.
   * The caller has to guarantee, that a stack not used by several provers
   * after calling {@link #close()}, because there is a dependency
   * from 'one' prover to 'one' (reusable) stack.
   */
  void close();
}
