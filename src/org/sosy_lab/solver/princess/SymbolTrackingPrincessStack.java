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

import static scala.collection.JavaConversions.iterableAsScalaIterable;

import ap.SimpleAPI;
import ap.parser.IFormula;
import ap.parser.IFunction;
import ap.parser.ITerm;

import org.sosy_lab.common.ShutdownNotifier;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

/** This is a Wrapper around some parts of the PrincessAPI.
 * It allows to have a stack with operations like:
 * push, pop, assert, checkSat, getInterpolants, getModel.
 * A stack is always connected with a PrincessEnvironment, because Variables are declared there.
 * One PrincessEnvironment can manage several stacks.
 *
 * <p>This implementation also tracks symbols
 * (boolean or integer variables, uninterpreted functions),
 * because in SMTLIB symbols would be deleted after a pop-operation.
 * We track symbols in our own stack and recreate them after the pop-operation. */
class SymbolTrackingPrincessStack {

  /** the wrapped api */
  private final PrincessEnvironment env;
  final SimpleAPI api;
  private final ShutdownNotifier shutdownNotifier;

  /** data-structures for tracking symbols */
  private final Deque<Level> trackingStack = new ArrayDeque<>();

  SymbolTrackingPrincessStack(
      final PrincessEnvironment env, final SimpleAPI api, ShutdownNotifier shutdownNotifier) {
    this.env = env;
    this.api = api;
    this.shutdownNotifier = shutdownNotifier;
  }

  public void push() {
    api.push();
    trackingStack.push(new Level());
  }

  /** This function pops levels from the assertion-stack. */
  public void pop() {
    // we have to recreate symbols on lower levels, because JavaSMT assumes "global" symbols.
    api.pop();
    Level level = trackingStack.pop();

    api.addBooleanVariables(iterableAsScalaIterable(level.booleanSymbols));
    api.addConstants(iterableAsScalaIterable(level.intSymbols));
    level.functionSymbols.forEach(api::addFunction);
    if (!trackingStack.isEmpty()) {
      trackingStack.peek().mergeWithHigher(level);
    }
  }

  /**
   * Clean the stack, such that it can be re-used.
   * The caller has to guarantee, that a stack not used by several provers
   * after calling {@link #close()}, because there is a dependency
   * from 'one' prover to 'one' (reusable) stack.
   */
  public void close() {
    // if a timeout is reached we do not want to do possibly long lasting
    // pop operations (with copying variables to lower tiers of the stack)
    if (shutdownNotifier.shouldShutdown()) {
      env.removeStack(this);
      api.shutDown();
    } else {
      for (int i = 0; i < trackingStack.size(); i++) {
        pop();
      }
      env.unregisterStack(this);
    }
  }

  /** add external definition: boolean variable. */
  void addSymbol(IFormula f) {
    api.addBooleanVariable(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().booleanSymbols.add(f);
    }
  }

  /** add external definition: integer variable. */
  void addSymbol(ITerm f) {
    api.addConstant(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().intSymbols.add(f);
    }
  }

  /** add external definition: uninterpreted function. */
  void addSymbol(IFunction f) {
    api.addFunction(f);
    if (!trackingStack.isEmpty()) {
      trackingStack.getLast().functionSymbols.add(f);
    }
  }

  private static class Level {
    List<IFormula> booleanSymbols = new ArrayList<>();
    List<ITerm> intSymbols = new ArrayList<>();
    List<IFunction> functionSymbols = new ArrayList<>();

    /**  add higher level to current level, we keep the order of creating symbols. */
    void mergeWithHigher(Level other) {
      this.booleanSymbols.addAll(other.booleanSymbols);
      this.intSymbols.addAll(other.intSymbols);
      this.functionSymbols.addAll(other.functionSymbols);
    }
  }
}
