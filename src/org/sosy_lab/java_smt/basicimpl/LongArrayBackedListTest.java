// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.testing.ListTestSuiteBuilder;
import com.google.common.collect.testing.TestStringListGenerator;
import com.google.common.collect.testing.features.CollectionFeature;
import com.google.common.collect.testing.features.CollectionSize;
import java.util.List;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class LongArrayBackedListTest extends TestCase {

  private static final TestStringListGenerator listGenerator =
      new TestStringListGenerator() {

        @Override
        protected List<String> create(final String[] pElements) {
          long[] backingArray = new long[pElements.length];
          for (int i = 0; i < backingArray.length; i++) {
            backingArray[i] = i;
          }
          return new LongArrayBackedList<>(backingArray) {
            @Override
            protected String convert(long pE) {
              return pElements[(int) pE];
            }
          };
        }
      };

  public static junit.framework.Test suite() {
    TestSuite suite = new TestSuite();

    suite.addTest(
        ListTestSuiteBuilder.using(listGenerator)
            .named("LongArrayBackedListList")
            .withFeatures(
                CollectionFeature.KNOWN_ORDER,
                CollectionFeature.ALLOWS_NULL_VALUES,
                CollectionSize.ANY)
            .createTestSuite());

    return suite;
  }
}
