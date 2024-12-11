// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.solvers.Solverless.SolverLessBooleanFormulaManager;

class SynchronizedFormulaManager implements FormulaManager {

  private final FormulaManager delegate;
  private final SolverContext sync;

  protected SynchronizedFormulaManager(FormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    synchronized (sync) {
      return new SynchronizedIntegerFormulaManager(delegate.getIntegerFormulaManager(), sync);
    }
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    synchronized (sync) {
      return new SynchronizedRationalFormulaManager(delegate.getRationalFormulaManager(), sync);
    }
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    synchronized (sync) {
      return new SynchronizedBooleanFormulaManager(delegate.getBooleanFormulaManager(), sync);
    }
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    synchronized (sync) {
      return new SynchronizedArrayFormulaManager(delegate.getArrayFormulaManager(), sync);
    }
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    synchronized (sync) {
      return new SynchronizedBitvectorFormulaManager(delegate.getBitvectorFormulaManager(), sync);
    }
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    synchronized (sync) {
      return new SynchronizedFloatingPointFormulaManager(
          delegate.getFloatingPointFormulaManager(), sync);
    }
  }

  @Override
  public UFManager getUFManager() {
    synchronized (sync) {
      return new SynchronizedUFManager(delegate.getUFManager(), sync);
    }
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    synchronized (sync) {
      return new SynchronizedSLFormulaManager(delegate.getSLFormulaManager(), sync);
    }
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    synchronized (sync) {
      return new SynchronizedQuantifiedFormulaManager(delegate.getQuantifiedFormulaManager(), sync);
    }
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    synchronized (sync) {
      return new SynchronizedStringFormulaManager(delegate.getStringFormulaManager(), sync);
    }
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    synchronized (sync) {
      return new SynchronizedEnumerationFormulaManager(
          delegate.getEnumerationFormulaManager(), sync);
    }
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> pFormulaType, String pName) {
    synchronized (sync) {
      return delegate.makeVariable(pFormulaType, pName);
    }
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> pDeclaration, List<? extends Formula> pArgs) {
    synchronized (sync) {
      return delegate.makeApplication(pDeclaration, pArgs);
    }
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> pDeclaration, Formula... pArgs) {
    synchronized (sync) {
      return delegate.makeApplication(pDeclaration, pArgs);
    }
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    synchronized (sync) {
      return delegate.getFormulaType(pFormula);
    }
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    synchronized (sync) {
      return delegate.parse(pS);
    }
  }

  @Override
  public BooleanFormula universalParseFromString(String pString)
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    return delegate.universalParseFromString(pString);
  }

  @Override
  public void dumpSMTLIB2() throws IOException {
    delegate.dumpSMTLIB2();
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String dump;
        synchronized (sync) {
          dump = delegate.dumpFormula(pT).toString(); // the work is done here
        }
        out.append(dump);
      }
    };
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula pInput, Tactic pTactic)
      throws InterruptedException {
    synchronized (sync) {
      return delegate.applyTactic(pInput, pTactic);
    }
  }

  @Override
  public <T extends Formula> T simplify(T pInput) throws InterruptedException {
    synchronized (sync) {
      return delegate.simplify(pInput);
    }
  }

  @Override
  public <R> R visit(Formula pF, FormulaVisitor<R> pFormulaVisitor) {
    synchronized (sync) {
      return delegate.visit(pF, pFormulaVisitor);
    }
  }

  @Override
  public void visitRecursively(Formula pF, FormulaVisitor<TraversalProcess> pFormulaVisitor) {
    synchronized (sync) {
      delegate.visitRecursively(pF, pFormulaVisitor);
    }
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T pF, FormulaTransformationVisitor pFormulaVisitor) {
    synchronized (sync) {
      return delegate.transformRecursively(pF, pFormulaVisitor);
    }
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula pF) {
    synchronized (sync) {
      return delegate.extractVariables(pF);
    }
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula pF) {
    synchronized (sync) {
      return delegate.extractVariablesAndUFs(pF);
    }
  }

  @Override
  public <T extends Formula> T substitute(
      T pF, Map<? extends Formula, ? extends Formula> pFromToMapping) {
    synchronized (sync) {
      return delegate.substitute(pF, pFromToMapping);
    }
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula pFormula, FormulaManager pOtherContext) {
    synchronized (sync) {
      return delegate.translateFrom(pFormula, pOtherContext);
    }
  }

  @Override
  public boolean isValidName(String pVariableName) {
    synchronized (sync) {
      return delegate.isValidName(pVariableName);
    }
  }

  @Override
  public String escape(String pVariableName) {
    synchronized (sync) {
      return delegate.escape(pVariableName);
    }
  }

  @Override
  public String unescape(String pVariableName) {
    synchronized (sync) {
      return delegate.unescape(pVariableName);
    }
  }
}
