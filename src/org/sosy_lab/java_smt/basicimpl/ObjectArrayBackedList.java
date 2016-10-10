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

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.errorprone.annotations.ForOverride;
import java.util.AbstractList;

/**
 * Immutable list that is backed by a <code>InnerT[]</code> and can have any
 * element type.
 * Sub-classes need to be defined and implement methods for creating
 * element instances from a long value.
 * These classes should not override any other methods to guarantee immutability.
 * @param <InnerT> The element type of the backing array.
 * @param <OuterT> The element type of the list.
 */
public abstract class ObjectArrayBackedList<InnerT, OuterT> extends AbstractList<OuterT> {

  private final InnerT[] array;

  /**
   * Create an instance backed by a given array.
   * For efficiency, the array is not copied and should thus not be changed afterwards.
   */
  protected ObjectArrayBackedList(InnerT[] pArray) {
    array = checkNotNull(pArray);
  }

  @ForOverride
  protected abstract OuterT convert(InnerT e);

  @Override
  public final OuterT get(int pIndex) {
    checkElementIndex(pIndex, array.length);
    return convert(array[pIndex]);
  }

  @Override
  public final int size() {
    return array.length;
  }
}
