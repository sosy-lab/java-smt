// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;

class SynchronizedBitvectorFormulaManager implements BitvectorFormulaManager {

  private final BitvectorFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedBitvectorFormulaManager(BitvectorFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, long pI) {
    synchronized (sync) {
      return delegate.makeBitvector(pLength, pI);
    }
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, BigInteger pI) {
    synchronized (sync) {
      return delegate.makeBitvector(pLength, pI);
    }
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, IntegerFormula pI) {
    synchronized (sync) {
      return delegate.makeBitvector(pLength, pI);
    }
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean pSigned) {
    synchronized (sync) {
      return delegate.toIntegerFormula(pI, pSigned);
    }
  }

  @Override
  public BitvectorFormula makeVariable(int pLength, String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pLength, pVar);
    }
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType pType, String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pType, pVar);
    }
  }

  @Override
  public int getLength(BitvectorFormula pNumber) {
    synchronized (sync) {
      return delegate.getLength(pNumber);
    }
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula pNumber) {
    synchronized (sync) {
      return delegate.negate(pNumber);
    }
  }

  @Override
  public BitvectorFormula add(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    synchronized (sync) {
      return delegate.add(pNumber1, pNumber2);
    }
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    synchronized (sync) {
      return delegate.subtract(pNumber1, pNumber2);
    }
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.divide(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BitvectorFormula rem(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.rem(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BitvectorFormula smod(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    synchronized (sync) {
      return delegate.smod(pNumber1, pNumber2);
    }
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    synchronized (sync) {
      return delegate.multiply(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula equal(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    synchronized (sync) {
      return delegate.equal(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.greaterThan(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.greaterOrEquals(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.lessThan(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    synchronized (sync) {
      return delegate.lessOrEquals(pNumber1, pNumber2, pSigned);
    }
  }

  @Override
  public BitvectorFormula not(BitvectorFormula pBits) {
    synchronized (sync) {
      return delegate.not(pBits);
    }
  }

  @Override
  public BitvectorFormula and(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    synchronized (sync) {
      return delegate.and(pBits1, pBits2);
    }
  }

  @Override
  public BitvectorFormula or(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    synchronized (sync) {
      return delegate.or(pBits1, pBits2);
    }
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    synchronized (sync) {
      return delegate.xor(pBits1, pBits2);
    }
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula pNumber, BitvectorFormula pToShift, boolean pSigned) {
    synchronized (sync) {
      return delegate.shiftRight(pNumber, pToShift, pSigned);
    }
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula pNumber, BitvectorFormula pToShift) {
    synchronized (sync) {
      return delegate.shiftLeft(pNumber, pToShift);
    }
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula pNumber, int pToRotate) {
    synchronized (sync) {
      return delegate.rotateLeft(pNumber, pToRotate);
    }
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula pNumber, BitvectorFormula pToRotate) {
    synchronized (sync) {
      return delegate.rotateLeft(pNumber, pToRotate);
    }
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula pNumber, int pToRotate) {
    synchronized (sync) {
      return delegate.rotateRight(pNumber, pToRotate);
    }
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula pNumber, BitvectorFormula pToRotate) {
    synchronized (sync) {
      return delegate.rotateRight(pNumber, pToRotate);
    }
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula pNumber, BitvectorFormula pAppend) {
    synchronized (sync) {
      return delegate.concat(pNumber, pAppend);
    }
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula pNumber, int pMsb, int pLsb) {
    synchronized (sync) {
      return delegate.extract(pNumber, pMsb, pLsb);
    }
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula pNumber, int pExtensionBits, boolean pSigned) {
    synchronized (sync) {
      return delegate.extend(pNumber, pExtensionBits, pSigned);
    }
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    synchronized (sync) {
      return delegate.distinct(pBits);
    }
  }
}
