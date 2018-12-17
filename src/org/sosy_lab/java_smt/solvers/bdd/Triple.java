/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.bdd;

import com.google.common.base.Objects;
import java.io.Serializable;


public class Triple<T1, T2, T3> implements Serializable {
  // default serial version
  private static final long serialVersionUID = 1L;
  private final T1 t1;
  private final T2 t2;
  private final T3 t3;

  private Triple(T1 t1, T2 t2, T3 t3) {
    this.t1 = t1;
    this.t2 = t2;
    this.t3 = t3;
  }


  public static <T1, T2, T3> Triple<T1, T2, T3> of(T1 t1, T2 t2, T3 t3) {
    return new Triple<>(t1, t2, t3);
  }

  public final T1 getFirst() {
    return t1;
  }

  public final T2 getSecond() {
    return t2;
  }

  public final T3 getThird() {
    return t3;
  }

  @Override
  public String toString() {
    return "(" + t1 + "," + t2 + "," + t3 + ")";
  }

  @Override
  public boolean equals(Object other) {
    return(other instanceof Triple<?,?,?>)
        && Objects.equal(t1, ((Triple<?, ?, ?>) other).t1)
        && Objects.equal(t2, ((Triple<?, ?, ?>) other).t2)
        && Objects.equal(t3, ((Triple<?, ?, ?>) other).t3);
  }

  @Override
  public int hashCode() {
    if (t1 == null && t2 == null) {
      return (t3 == null) ? 0 : t3.hashCode() + 1;
    } else if (t1 == null && t3 == null) {
      return t2.hashCode() + 2;
    } else if (t1 == null) {
      return t2.hashCode() * 7 + t3.hashCode();
    } else if (t2 == null && t3 == null) {
      return t1.hashCode() + 3;
    } else if (t2 == null) {
      return t1.hashCode() * 11 + t3.hashCode();
    } else if (t3 == null) {
      return t1.hashCode() * 13 + t2.hashCode();
    } else {
      return t1.hashCode() * 17 + t2.hashCode() * 5 + t3.hashCode();
    }
}
}
