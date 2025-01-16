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

package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import org.sosy_lab.java_smt.api.Formula;

public enum FormulaTypesForChecking {
  REGEX,
  STRING,
  FLOATING_POINT,
  INTEGER,
  BITVECTOR,
  ARRAY,
  RATIONAL,
  BOOLEAN,
  DUMMY;

  public String parseToSMTLIBFormulaType(){
    switch (this){
        case REGEX:
          return "Regex";
        case STRING:
          return "String";
        case FLOATING_POINT:
          return "(_ FloatingPoint ";
        case INTEGER:
          return "Int";
        case BITVECTOR:
          return "(_ BitVec ";
        case ARRAY:
          return "Array";
        case RATIONAL:
          return "Real";
        case BOOLEAN:
          return "Bool";
        default:
          throw new UnsupportedOperationException("Unsupported formula type");
    }
  }
}
