// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

@SuppressWarnings("ClassTypeParameterName")
class SynchronizedNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {

  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;
  final SolverContext sync;

  SynchronizedNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public ResultFormulaType makeNumber(long pNumber) {
    synchronized (sync) {
      return delegate.makeNumber(pNumber);
    }
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger pNumber) {
    synchronized (sync) {
      return delegate.makeNumber(pNumber);
    }
  }

  @Override
  public ResultFormulaType makeNumber(double pNumber) {
    synchronized (sync) {
      return delegate.makeNumber(pNumber);
    }
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal pNumber) {
    synchronized (sync) {
      return delegate.makeNumber(pNumber);
    }
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    synchronized (sync) {
      return delegate.makeNumber(pI);
    }
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    synchronized (sync) {
      return delegate.makeNumber(pRational);
    }
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pVar);
    }
  }

  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    synchronized (sync) {
      return delegate.getFormulaType();
    }
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType pNumber) {
    synchronized (sync) {
      return delegate.negate(pNumber);
    }
  }

  @Override
  public ResultFormulaType add(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.add(pNumber1, pNumber2);
    }
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> pOperands) {
    synchronized (sync) {
      return delegate.sum(pOperands);
    }
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.subtract(pNumber1, pNumber2);
    }
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.divide(pNumber1, pNumber2);
    }
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.multiply(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula equal(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.equal(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    synchronized (sync) {
      return delegate.distinct(pNumbers);
    }
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.greaterThan(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.greaterOrEquals(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.lessThan(pNumber1, pNumber2);
    }
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    synchronized (sync) {
      return delegate.lessOrEquals(pNumber1, pNumber2);
    }
  }

  @Override
  public IntegerFormula floor(ParamFormulaType pNumber) {
    synchronized (sync) {
      return delegate.floor(pNumber);
    }
  }

  @Override
  public RationalFormula toRational(ParamFormulaType formula) {
    synchronized (sync) {
      return delegate.toRational(formula);
    }
  }
}
