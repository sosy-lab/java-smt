// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.auto.value.AutoValue;
import java.util.Objects;

@AutoValue
public abstract class InterpolationPoint<T> {
  public static <T> InterpolationPoint<T> create(T reference) {
    return new AutoValue_InterpolationPoint<>(reference);
  }

  public abstract T getReference();

  @Override
  public final String toString() {
    return Objects.toString(getReference());
  }
}
