/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class SynchronizedBooleanFormulaManager implements BooleanFormulaManager {

  private final BooleanFormulaManager delegate;
  private final SolverContext sync;

  private final BooleanFormula tru;
  private final BooleanFormula fls;

  SynchronizedBooleanFormulaManager(BooleanFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
    tru = delegate.makeTrue();
    fls = delegate.makeFalse();
  }

  @Override
  public BooleanFormula makeTrue() {
    return tru;
  }

  @Override
  public BooleanFormula makeFalse() {
    return fls;
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pVar);
    }
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula pFormula1, BooleanFormula pFormula2) {
    synchronized (sync) {
      return delegate.equivalence(pFormula1, pFormula2);
    }
  }

  @Override
  public BooleanFormula implication(BooleanFormula pFormula1, BooleanFormula pFormula2) {
    synchronized (sync) {
      return delegate.implication(pFormula1, pFormula2);
    }
  }

  @Override
  public boolean isTrue(BooleanFormula pFormula) {
    if (pFormula == tru) {
      return true;
    }
    synchronized (sync) {
      return delegate.isTrue(pFormula);
    }
  }

  @Override
  public boolean isFalse(BooleanFormula pFormula) {
    if (pFormula == fls) {
      return true;
    }
    synchronized (sync) {
      return delegate.isFalse(pFormula);
    }
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula pCond, T pF1, T pF2) {
    synchronized (sync) {
      return delegate.ifThenElse(pCond, pF1, pF2);
    }
  }

  @Override
  public BooleanFormula not(BooleanFormula pBits) {
    synchronized (sync) {
      return delegate.not(pBits);
    }
  }

  @Override
  public BooleanFormula and(BooleanFormula pBits1, BooleanFormula pBits2) {
    synchronized (sync) {
      return delegate.and(pBits1, pBits2);
    }
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> pBits) {
    synchronized (sync) {
      return delegate.and(pBits);
    }
  }

  @Override
  public BooleanFormula and(BooleanFormula... pBits) {
    synchronized (sync) {
      return delegate.and(pBits);
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  public BooleanFormula or(BooleanFormula pBits1, BooleanFormula pBits2) {
    synchronized (sync) {
      return delegate.or(pBits1, pBits2);
    }
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> pBits) {
    synchronized (sync) {
      return delegate.or(pBits);
    }
  }

  @Override
  public BooleanFormula or(BooleanFormula... pBits) {
    synchronized (sync) {
      return delegate.or(pBits);
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  public BooleanFormula xor(BooleanFormula pBits1, BooleanFormula pBits2) {
    synchronized (sync) {
      return delegate.xor(pBits1, pBits2);
    }
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> pVisitor) {
    synchronized (sync) {
      return delegate.visit(pFormula, pVisitor);
    }
  }

  @Override
  public void visitRecursively(
      BooleanFormula pF, BooleanFormulaVisitor<TraversalProcess> pRFormulaVisitor) {
    synchronized (sync) {
      delegate.visitRecursively(pF, pRFormulaVisitor);
    }
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula pF, BooleanFormulaTransformationVisitor pVisitor) {
    synchronized (sync) {
      return delegate.transformRecursively(pF, pVisitor);
    }
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula pF, boolean pFlatten) {
    synchronized (sync) {
      return delegate.toConjunctionArgs(pF, pFlatten);
    }
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula pF, boolean pFlatten) {
    synchronized (sync) {
      return delegate.toDisjunctionArgs(pF, pFlatten);
    }
  }
}
