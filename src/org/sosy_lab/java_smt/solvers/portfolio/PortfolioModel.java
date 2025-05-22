/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;

public class PortfolioModel implements Model, Evaluator {

  // Not created on the current thread, so reuse will most likely fail
  private final ImmutableList<ValueAssignment> model;
  private final Solvers generatingSolver;

  PortfolioModel(ImmutableList<ValueAssignment> pModel, Solvers pSolver) {
    model = pModel;
    generatingSolver = pSolver;
  }

  public Solvers getGeneratingSolver() {
    return generatingSolver;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable Object evaluate(Formula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable String evaluate(StringFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public void close() {
    // Nothing to do
  }
}
