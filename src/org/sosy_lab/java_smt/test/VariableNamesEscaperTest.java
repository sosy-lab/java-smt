// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.Lists;
import java.util.List;
import org.junit.Test;

/** inherits many tests from {@link VariableNamesTest}. */
public class VariableNamesEscaperTest extends VariableNamesTest {
  @Override
  boolean allowInvalidNames() {
    return false;
  }

  @Override
  protected List<String> getAllNames() {
    return Lists.transform(super.getAllNames(), mgr::escape);
  }

  @Test
  public void testEscapeUnescape() {
    for (String var : getAllNames()) {
      assertThat(mgr.unescape(mgr.escape(var))).isEqualTo(var);
      assertThat(mgr.unescape(mgr.unescape(mgr.escape(mgr.escape(var))))).isEqualTo(var);
    }
  }

  @Test
  public void testDoubleEscapeUnescape() {
    for (String var : getAllNames()) {
      assertThat(mgr.unescape(mgr.escape(var))).isEqualTo(var);
      assertThat(mgr.unescape(mgr.unescape(mgr.escape(mgr.escape(var))))).isEqualTo(var);
    }
  }
}
