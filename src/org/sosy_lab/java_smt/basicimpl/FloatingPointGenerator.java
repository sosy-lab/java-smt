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

package org.sosy_lab.java_smt.basicimpl;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class FloatingPointGenerator {
  private FloatingPointGenerator() {}
  protected static void logMakeFloatingPoint(Object result, int exponent, int mantissa) {
  }
  /*
  protected static void logMakeBitVector(Object result, int length, BigInteger i) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(Long.toString(length));
    inputParams.add(i.toString());
    Function<List<Object>, String> functionToString =
        inPlaceInputParamsString -> {
          // FIXME Fix the conversion to String
          String formatString = "%0" + length + "d";
          BigInteger binaryNumber =
              new BigInteger(
                  Long.toBinaryString(parseLong((String) inPlaceInputParamsString.get(1))));
          return "#b" + String.format(formatString, binaryNumber);
        };
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }
   */
}
