// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron.types;

/**
 * This is a helper-class for defining the integer, rational and boolean type for the Generics of
 * ApronFormulaCreator.
 */
public interface ApronFormulaType {

  FormulaType getType();

  enum FormulaType {
    BOOLEAN,
    INTEGER,
    RATIONAL
  }

  class ApronIntegerType implements ApronFormulaType {

    public ApronIntegerType() {}

    @Override
    public FormulaType getType() {
      return FormulaType.INTEGER;
    }
  }

  class ApronRationalType implements ApronFormulaType {

    public ApronRationalType() {}

    @Override
    public FormulaType getType() {
      return FormulaType.RATIONAL;
    }
  }

  class ApronBooleanType implements ApronFormulaType {

    public ApronBooleanType() {}

    @Override
    public FormulaType getType() {
      return FormulaType.BOOLEAN;
    }
  }
}
