
package org.sosy_lab.java_smt.solvers.bdd;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.function.Function;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * RegionManager that synchronizes and sequentializes all accesses to the delegating
 * {@link RegionManager}.
 */
public class SynchronizedRegionManager implements RegionManager {

  private final RegionManager delegate;

  public SynchronizedRegionManager(RegionManager pDelegate) {
    delegate = pDelegate;
  }

  @Override
  public RegionBuilder builder(ShutdownNotifier pShutdownNotifier) {
    synchronized (delegate) {
      return delegate.builder(pShutdownNotifier);
    }
  }

  @Override
  public Region makeTrue() {
    synchronized (delegate) {
      return delegate.makeTrue();
    }
  }

  @Override
  public Region makeFalse() {
    synchronized (delegate) {
      return delegate.makeFalse();
    }
  }

  @Override
  public Region makeNot(Region pF) {
    synchronized (delegate) {
      return delegate.makeNot(pF);
    }
  }

  @Override
  public Region makeAnd(Region pF1, Region pF2) {
    synchronized (delegate) {
      return delegate.makeAnd(pF1, pF2);
    }
  }

  @Override
  public Region makeOr(Region pF1, Region pF2) {
    synchronized (delegate) {
      return delegate.makeOr(pF1, pF2);
    }
  }

  @Override
  public Region makeEqual(Region pF1, Region pF2) {
    synchronized (delegate) {
      return delegate.makeEqual(pF1, pF2);
    }
  }

  @Override
  public Region makeUnequal(Region pF1, Region pF2) {
    synchronized (delegate) {
      return delegate.makeUnequal(pF1, pF2);
    }
  }

  @Override
  public Region makeIte(Region pF1, Region pF2, Region pF3) {
    synchronized (delegate) {
      return delegate.makeIte(pF1, pF2, pF3);
    }
  }

  @Override
  public Region makeExists(Region pF1, Region... pF2) {
    synchronized (delegate) {
      return delegate.makeExists(pF1, pF2);
    }
  }

  @Override
  public boolean entails(Region pF1, Region pF2) throws SolverException, InterruptedException {
    synchronized (delegate) {
      return delegate.entails(pF1, pF2);
    }
  }

  @Override
  public Region createPredicate() {
    synchronized (delegate) {
      return delegate.createPredicate();
    }
  }

  @Override
  public Region fromFormula(
      BooleanFormula pF,
      FormulaManagerView pFmgr,
      Function<BooleanFormula, Region> pAtomToRegion) {
    synchronized (delegate) {
      return delegate.fromFormula(pF, pFmgr, pAtomToRegion);
    }
  }

  @Override
  public Triple<Region, Region, Region> getIfThenElse(Region pF) {
    synchronized (delegate) {
      return delegate.getIfThenElse(pF);
    }
  }

  @Override
  public void printStatistics(PrintStream pOut) {
    synchronized (delegate) {
      delegate.printStatistics(pOut);
    }
  }

  @Override
  public String getVersion() {
    synchronized (delegate) {
      return delegate.getVersion();
    }
  }

  @Override
  public void setVarOrder(ArrayList<Integer> pOrder) {
    synchronized (delegate) {
      delegate.setVarOrder(pOrder);
    }
  }

  @Override
  public void reorder(PredicateOrderingStrategy pStrategy) {
    synchronized (delegate) {
      delegate.reorder(pStrategy);
    }
  }
}
