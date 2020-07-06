// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.errorprone.annotations.ForOverride;
import java.util.AbstractList;
import java.util.RandomAccess;

/**
 * Immutable list that is backed by a <code>long[]</code> and can have any element type. Sub-classes
 * need to be defined and implement methods for creating element instances from a long value. These
 * classes should not override any other methods to guarantee immutability.
 *
 * @param <E> The element type.
 */
public abstract class LongArrayBackedList<E> extends AbstractList<E> implements RandomAccess {

  private final long[] array;

  /**
   * Create an instance backed by a given array. For efficiency, the array is not copied and should
   * thus not be changed afterwards.
   */
  protected LongArrayBackedList(long[] pArray) {
    array = checkNotNull(pArray);
  }

  @ForOverride
  protected abstract E convert(long e);

  @Override
  public final E get(int pIndex) {
    checkElementIndex(pIndex, array.length);
    return convert(array[pIndex]);
  }

  @Override
  public final int size() {
    return array.length;
  }
}
