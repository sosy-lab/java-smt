/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Joiner;
import com.google.errorprone.annotations.Immutable;
import java.util.Map;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;

@SuppressWarnings({"unchecked", "Immutable"})
@Immutable
public class PortfolioFormula implements Formula {

  private final Map<Solvers, ? extends Formula> formulasPerSolver;

  PortfolioFormula(final Map<Solvers, ? extends Formula> pFormulaPerSolver) {
    checkNotNull(pFormulaPerSolver);
    checkState(!pFormulaPerSolver.isEmpty());
    formulasPerSolver = pFormulaPerSolver;
  }

  @Override
  public final String toString() {
    return Joiner.on(System.lineSeparator()).withKeyValueSeparator(": ").join(formulasPerSolver);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof PortfolioFormula)) {
      return false;
    }
    return formulasPerSolver.equals(((PortfolioFormula) o).formulasPerSolver);
  }

  @Override
  public final int hashCode() {
    return formulasPerSolver.hashCode();
  }

  Map<Solvers, ? extends Formula> getFormulasPerSolver() {
    return formulasPerSolver;
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class PortfolioArrayFormula<TI extends Formula, TE extends Formula>
      extends PortfolioFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    PortfolioArrayFormula(
        Map<Solvers, ? extends Formula> pFormulasPerSolver,
        FormulaType<TI> pIndexType,
        FormulaType<TE> pElementType) {
      super(pFormulasPerSolver);
      indexType = pIndexType;
      elementType = pElementType;
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }

    @Override
    Map<Solvers, ArrayFormula<TI, TE>> getFormulasPerSolver() {
      return (Map<Solvers, ArrayFormula<TI, TE>>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioBitvectorFormula extends PortfolioFormula
      implements BitvectorFormula {
    PortfolioBitvectorFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, BitvectorFormula> getFormulasPerSolver() {
      return (Map<Solvers, BitvectorFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioFloatingPointFormula extends PortfolioFormula
      implements FloatingPointFormula {
    PortfolioFloatingPointFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, FloatingPointFormula> getFormulasPerSolver() {
      return (Map<Solvers, FloatingPointFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioFloatingPointRoundingModeFormula extends PortfolioFormula
      implements FloatingPointRoundingModeFormula {
    PortfolioFloatingPointRoundingModeFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, FloatingPointRoundingModeFormula> getFormulasPerSolver() {
      return (Map<Solvers, FloatingPointRoundingModeFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioIntegerFormula extends PortfolioFormula implements IntegerFormula {
    PortfolioIntegerFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, IntegerFormula> getFormulasPerSolver() {
      return (Map<Solvers, IntegerFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioRationalFormula extends PortfolioFormula implements RationalFormula {
    PortfolioRationalFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, RationalFormula> getFormulasPerSolver() {
      return (Map<Solvers, RationalFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioBooleanFormula extends PortfolioFormula implements BooleanFormula {
    PortfolioBooleanFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, BooleanFormula> getFormulasPerSolver() {
      return (Map<Solvers, BooleanFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioEnumerationFormula extends PortfolioFormula
      implements EnumerationFormula {
    PortfolioEnumerationFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, EnumerationFormula> getFormulasPerSolver() {
      return (Map<Solvers, EnumerationFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioStringFormula extends PortfolioFormula implements StringFormula {
    PortfolioStringFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, StringFormula> getFormulasPerSolver() {
      return (Map<Solvers, StringFormula>) super.formulasPerSolver;
    }
  }

  @Immutable
  static final class PortfolioRegexFormula extends PortfolioFormula implements RegexFormula {
    PortfolioRegexFormula(Map<Solvers, ? extends Formula> pFormulasPerSolver) {
      super(pFormulasPerSolver);
    }

    @Override
    Map<Solvers, RegexFormula> getFormulasPerSolver() {
      return (Map<Solvers, RegexFormula>) super.formulasPerSolver;
    }
  }
}
