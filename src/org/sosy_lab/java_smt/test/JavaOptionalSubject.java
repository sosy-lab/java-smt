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

import com.google.common.truth.FailureStrategy;
import com.google.common.truth.Subject;

import java.util.Optional;

import javax.annotation.Nullable;

/**
 * Optional subject for Java8 {@link Optional}.
 * Mirrors {@link com.google.common.truth.GuavaOptionalSubject},
 * yet works for another kind of optional.
 */
@Deprecated // Uses Truth8's OptionalSubject instead
public class JavaOptionalSubject extends Subject<JavaOptionalSubject, Optional<?>> {
  JavaOptionalSubject(FailureStrategy failureStrategy, @Nullable Optional<?> subject) {
    super(failureStrategy, subject);
  }

  public void isPresent() {
    if (this.actual() == null || !this.actual().isPresent()) {
      this.failWithoutActual("is present");
    }
  }

  public void isAbsent() {
    if (this.actual() == null || this.actual().isPresent()) {
      this.fail("is absent");
    }
  }

  public void hasValue(Object expected) {
    if (expected == null) {
      throw new NullPointerException("Optional cannot have a null value.");
    } else {
      if (this.actual() != null && (this.actual()).isPresent()) {
        Object actual = this.actual().get();
        if (!actual.equals(expected)) {
          this.fail("has value", expected);
        }
      } else {
        this.fail("has value", expected);
      }
    }
  }
}
