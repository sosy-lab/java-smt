/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.api;

import java.util.List;

/**
 * Function declaration,
 * for both UFs and built-in functions (theory and boolean).
 *
 * <p>Can be instantiated using {@link FormulaManager#makeApplication}
 */
public interface FunctionDeclaration<E extends Formula> {

  /**
   * @return Type of the function (LT / GT / UF / etc...).
   */
  FunctionDeclarationKind getKind();

  /**
   * @return Name of the function (UF name / "LT" / etc...).
   */
  String getName();

  /**
   * @return Sort of the function output.
   */
  FormulaType<E> getType();

  /**
   * @return Sorts of the arguments.
   */
  List<FormulaType<?>> getArgumentTypes();
}
