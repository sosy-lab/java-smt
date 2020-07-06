// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api.visitors;

import com.google.common.collect.ImmutableSet;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;

/**
 * Return class that lets the visitor guide the recursive formula traversal process started with
 * {@link FormulaManager#visitRecursively}. or {@link BooleanFormulaManager#visitRecursively}.
 */
public final class TraversalProcess {
  /** Continue traversal and recurse into current formula subtree. */
  public static final TraversalProcess CONTINUE =
      new TraversalProcess(TraversalType.CONTINUE_TYPE, ImmutableSet.of());

  /** Continue traversal, but do not recurse into current formula subtree. */
  public static final TraversalProcess SKIP =
      new TraversalProcess(TraversalType.SKIP_TYPE, ImmutableSet.of());

  /** Immediately abort traversal and return to caller. */
  public static final TraversalProcess ABORT =
      new TraversalProcess(TraversalType.ABORT_TYPE, ImmutableSet.of());

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

  public enum TraversalType {
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

  public TraversalType getType() {
    return type;
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
