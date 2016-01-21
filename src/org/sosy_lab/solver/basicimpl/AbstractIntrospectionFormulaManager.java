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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;
import com.google.common.collect.Lists;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.List;

public abstract class AbstractIntrospectionFormulaManager<TFormulaInfo, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv> {

  protected AbstractIntrospectionFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv> creator) {
    super(creator);
  }

  public <R> R visit(FormulaVisitor<R> visitor, Formula input) {
    return visit(visitor, input, getFormulaCreator().extractInfo(input));
  }

  protected void visitRecursively(FormulaVisitor<TraversalProcess> pFormulaVisitor, Formula pF) {
    RecursiveFormulaVisitor recVisitor = new RecursiveFormulaVisitor(pFormulaVisitor);
    recVisitor.addToQueue(pF);
    while (!recVisitor.isQueueEmpty()) {
      TraversalProcess process = checkNotNull(visit(recVisitor, recVisitor.pop()));
      if (process == TraversalProcess.ABORT) {
        return;
      }
    }
  }

  protected abstract <R> R visit(FormulaVisitor<R> visitor, Formula input, TFormulaInfo f);

  protected List<TFormulaInfo> extractInfo(List<Formula> input) {
    return Lists.transform(
        input,
        new Function<Formula, TFormulaInfo>() {
          @Override
          public TFormulaInfo apply(Formula formula) {
            return extractInfo(formula);
          }
        });
  }
}
