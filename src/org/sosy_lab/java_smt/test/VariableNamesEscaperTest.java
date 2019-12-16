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

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Test;

/** inherits many tests from {@link VariableNamesTest}. */
public class VariableNamesEscaperTest extends VariableNamesTest {

  @Override
  boolean allowInvalidNames() {
    return false;
  }

  @Override
  String getVarname() {
    return mgr.escape(super.getVarname());
  }

  @Test
  public void testEscapeUnescape() {
    String var = super.getVarname();
    assertThat(mgr.unescape(mgr.escape(var))).isEqualTo(var);
    assertThat(mgr.unescape(mgr.unescape(mgr.escape(mgr.escape(var))))).isEqualTo(var);
  }

  @Test
  public void testDoubleEscapeUnescape() {
    String var = getVarname();
    assertThat(mgr.unescape(mgr.escape(var))).isEqualTo(var);
    assertThat(mgr.unescape(mgr.unescape(mgr.escape(mgr.escape(var))))).isEqualTo(var);
  }
}
