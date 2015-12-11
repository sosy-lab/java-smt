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
package org.sosy_lab.solver.api;

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

/**
 * Instances of this interface provide direct low-level access to an SMT solver.
 */
public interface FormulaManager {

  /**
   * Returns the Integer-Theory.
   * Because most SAT-solvers support automatic casting between Integer- and Rational-Theory,
   * the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL and others.
   */
  NumeralFormulaManager<IntegerFormula, IntegerFormula> getIntegerFormulaManager();

  /**
   * Returns the Rational-Theory.
   * Because most SAT-solvers support automatic casting between Integer- and Rational-Theory,
   * the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL, etc.
   */
  NumeralFormulaManager<NumeralFormula, RationalFormula> getRationalFormulaManager();

  /**
   * Returns the Boolean-Theory.
   */
  BooleanFormulaManager getBooleanFormulaManager();

  /**
   * Returns the Array-Theory.
   */
  ArrayFormulaManager getArrayFormulaManager();

  /**
   * Returns the Bitvector-Theory.
   */
  BitvectorFormulaManager getBitvectorFormulaManager();

  /**
   * Returns the Floating-Point-Theory.
   */
  FloatingPointFormulaManager getFloatingPointFormulaManager();

  /**
   * Returns the Function-Theory.
   */
  FunctionFormulaManager getFunctionFormulaManager();

  /**
   * Returns some unsafe traverse methods.
   */
  UnsafeFormulaManager getUnsafeFormulaManager();

  /**
   * Returns the interface for handling quantifiers.
   */
  QuantifiedFormulaManager getQuantifiedFormulaManager();

  /**
   * Create a fresh new {@link ProverEnvironment} which encapsulates an assertion stack
   * and can be used to check formulas for unsatisfiability.
   * @param generateModels Whether the solver should generate models (i.e., satisfying assignments)
   *     for satisfiable formulas.
   * @param generateUnsatCore Whether the solver should generate an unsat core
   *     for unsatisfiable formulas.
   */
  ProverEnvironment newProverEnvironment(boolean generateModels, boolean generateUnsatCore);

  /**
   * Create a fresh new {@link InterpolatingProverEnvironment} which encapsulates an assertion stack
   * and allows to generate and retrieve interpolants for unsatisfiable formulas.
   * If the SMT solver is able to handle satisfiability tests with assumptions please consider
   * implementing the {@link InterpolatingProverEnvironmentWithAssumptions} interface, and return
   * an Object of this type here.
   * @param shared Whether the solver should share as much as possible with other environments.
   */
  InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(boolean shared);

  /**
   * Create a fresh new {@link OptEnvironment} which encapsulates an assertion stack
   * and allows to solve optimization queries.
   */
  OptEnvironment newOptEnvironment();

  /**
   * Returns the type of the given Formula.
   */
  <T extends Formula> FormulaType<T> getFormulaType(T formula);

  /**
   * Parse a boolean formula given as a String in an SMT-LIB file format.
   * @return The same formula in the internal representation.
   * @throws IllegalArgumentException If the string cannot be parsed.
   */
  BooleanFormula parse(String s) throws IllegalArgumentException;

  /**
   * @return SMT-LIB formula serialization.
   *
   * To get a String, simply call {@link Object#toString()}
   * on the returned object.
   * This method is lazy and does not create an output string until the returned
   * object is actually used.
   */
  Appender dumpFormula(BooleanFormula pT);

  /**
   * Get version information out of the solver.
   */
  String getVersion();

  /** Apply a tactic which performs formula transformation */
  BooleanFormula applyTactic(BooleanFormula input, Tactic tactic);

  /** Strategies for transforming the formula AST. */
  enum Tactic {
    NNF("nnf", "Convert the formula to NNF"),
    CNF("tseitin-cnf", "Convert the formula to CNF using Tseitin encoding"),
    QE_LIGHT("qe-light", "Perform light quantifier elimination"),
    QE("qe", "Perform quantifier elimination");

    private final String name;
    private final String description;

    Tactic(String pName, String pDescription) {
      name = pName;
      description = pDescription;
    }

    public String getTacticName() {
      return name;
    }

    public String getDescription() {
      return description;
    }
  }
}
