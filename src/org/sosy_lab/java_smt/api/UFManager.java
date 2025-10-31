// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableList;
import java.util.List;

/** Manager for dealing with uninterpreted functions (UFs). */
public interface UFManager {

  /** Declare an uninterpreted function. */
  <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args);

  /** Declare an uninterpreted function. */
  default <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, FormulaType<?>... args) {
    return declareUF(name, returnType, ImmutableList.copyOf(args));
  }

  /**
   * Create an uninterpreted function call.
   *
   * <p>Simply delegates to {@link FormulaManager#makeApplication(FunctionDeclaration, List)}
   *
   * @param funcType Declaration of the function to call.
   * @param args Arguments of the function.
   * @return Instantiated function call.
   */
  <T extends Formula> T callUF(FunctionDeclaration<T> funcType, List<? extends Formula> args);

  /**
   * @see #callUF(FunctionDeclaration, List)
   */
  default <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return callUF(funcType, ImmutableList.copyOf(args));
  }

  /**
   * Declares and calls an uninterpreted function with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs);

  /**
   * @see #declareAndCallUF(String, FormulaType, List)
   */
  default <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    return declareAndCallUF(name, pReturnType, ImmutableList.copyOf(pArgs));
  }
}
