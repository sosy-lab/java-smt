/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.solver.cvc4;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Kind;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

public class CVC4Util {

  private CVC4Util() {}

  public static Set<Expr> getVarsAndUIFs(Collection<Expr> termList) {
    Set<Expr> result = new HashSet<>();
    Set<Expr> seen = new HashSet<>();
    Deque<Expr> todo = new ArrayDeque<>(termList);

    while (!todo.isEmpty()) {
      Expr t = todo.removeLast();
      if (!seen.add(t)) {
        continue;
      }

      // variable or uf
      if (t.isVariable() || (!t.isConst() && t.getKind().equals(Kind.APPLY_UF))) {
        result.add(t);
      }

      // if this is a function we need to dive into it
      if (t.getNumChildren() > 0) {
        for (long i = 0; i < t.getNumChildren(); i++) {
          todo.addLast(t.getChild(i));
        }
      }
    }
    return result;
  }
}
