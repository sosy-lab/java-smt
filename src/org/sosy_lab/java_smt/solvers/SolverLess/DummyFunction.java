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

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.List;
import java.util.Objects;

public class DummyFunction {
  private String name;
  private DummyType returnType;
  private List<DummyType> argumentTypes;
  public DummyFunction() {}

  public String getName() {
    return name;
  }

  public void setName(String name) {
    this.name = name;
  }

  public DummyType getReturnType() {
    return returnType;
  }

  public void setReturnType(DummyType returnType) {
    this.returnType = returnType;
  }

  public List<DummyType> getArgumentTypes() {
    return argumentTypes;
  }

  public void setArgumentTypes(List<DummyType> argumentTypes) {
    this.argumentTypes = argumentTypes;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Function Name: ").append(name).append(", Return Type: ").append(returnType);
    if (argumentTypes != null && !argumentTypes.isEmpty()) {
      sb.append(", Argument Types: ").append(argumentTypes);
    }
    return sb.toString();
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof DummyFunction)) return false;
    DummyFunction that = (DummyFunction) o;
    return Objects.equals(name, that.name) &&
        Objects.equals(returnType, that.returnType) &&
        Objects.equals(argumentTypes, that.argumentTypes);
  }

  @Override
  public int hashCode() {
    return Objects.hash(name, returnType, argumentTypes);
  }
}
