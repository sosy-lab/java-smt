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

import org.sosy_lab.solver.api.FormulaManager;

/**
 * Enum that lets the visitor guide the recursive formula traversal process
 * started with
 * {@link FormulaManager#visitRecursively(FormulaVisitor, org.sosy_lab.solver.api.Formula)}.
 */
public enum TraversalProcess {
  /**
   * Continue traversal and recurse into current formula subtree.
   */
  CONTINUE,

  /**
   * Continue traversal, but do not recurse into current formula subtree.
   */
  SKIP,

  /**
   * Immediately abort traversal and return to caller.
   */
  ABORT;
}
