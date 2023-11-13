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

package org.sosy_lab.java_smt.test;


import static com.google.common.truth.Truth.assertThat;

import java.util.Objects;
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.utils.Generators.Generator;


public class ArraySMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /**
   * Integer and Rationals not supported by BOOLECTOR
   * Rationals not supported by PRINCESS
   * Z3 runs only when executed separately from other solvers
   */

  public void clearGenerator() {
    Generator.lines.delete(0, Generator.lines.length());
    Generator.registeredVariables.clear();
    Generator.executedAggregator.clear();
  }

  @Test
  public void testMakeArray() {
    requireArrays();
    clearGenerator();
    //ArrayFormula<IntegerFormula, IntegerFormula> a =


    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "";

    assertThat(actualResult).isEqualTo(expectedResult);
    }
}