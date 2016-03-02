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
package org.sosy_lab.solver.visitors;

import com.google.common.collect.ImmutableSet;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;

/**
 * Return class that lets the visitor guide the recursive formula traversal process
 * started with
 * {@link FormulaManager#visitRecursively(FormulaVisitor, org.sosy_lab.solver.api.Formula)}.
 * or
 * {@link BooleanFormulaManager#visitRecursively(BooleanFormulaVisitor, BooleanFormula)}.
 */
public class TraversalProcess {
  /**
   * Continue traversal and recurse into current formula subtree.
   */
  public static final TraversalProcess CONTINUE =
      new TraversalProcess(TraversalType.CONTINUE_TYPE, ImmutableSet.<Formula>of());

  /**
   * Continue traversal, but do not recurse into current formula subtree.
   */
  public static final TraversalProcess SKIP =
      new TraversalProcess(TraversalType.SKIP_TYPE, ImmutableSet.<Formula>of());

  /**
   * Immediately abort traversal and return to caller.
   */
  public static final TraversalProcess ABORT =
      new TraversalProcess(TraversalType.ABORT_TYPE, ImmutableSet.<Formula>of());

  /**
   * Traverse only the given children.
   *
   * <p>NOTE: given formulas which are <em>not</em> children of the given node will be ignored.
   */
  public static TraversalProcess custom(Iterable<? extends Formula> pToTraverse) {
    return new TraversalProcess(TraversalType.CUSTOM_TYPE, ImmutableSet.copyOf(pToTraverse));
  }

  /**
   * Traverse only the given child.
   *
   * <p>NOTE: any given which is <em>not</em> child of the given node will be ignored.
   */
  public static TraversalProcess custom(Formula pToTraverse) {
    return new TraversalProcess(TraversalType.CUSTOM_TYPE, ImmutableSet.of(pToTraverse));
  }

  private enum TraversalType {
    CONTINUE_TYPE,
    SKIP_TYPE,
    ABORT_TYPE,
    CUSTOM_TYPE
  }

  private final TraversalType type;
  private final ImmutableSet<? extends Formula> toTraverse;

  private TraversalProcess(TraversalType pType, ImmutableSet<? extends Formula> pToTraverse) {
    type = pType;
    toTraverse = pToTraverse;
  }

  public boolean contains(Formula f) {
    if (type == TraversalType.CONTINUE_TYPE) {
      return true;
    } else if (type == TraversalType.SKIP_TYPE || type == TraversalType.ABORT_TYPE) {
      return false;
    } else {
      assert type == TraversalType.CUSTOM_TYPE;
      return toTraverse.contains(f);
    }
  }
}
