/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.native_api.stp.ifaceflag_t;
import org.sosy_lab.java_smt.native_api.stp.stpJapi;

public class StpNativeApiTest {

  @BeforeClass
  public static void loadOpensmt2Library() {
    try {
      NativeLibraries.loadLibrary("stpJapi");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Cannot find at the STP native library", e);
    }
  }

  @Test
  public void testStpGitVersion() throws Exception {
    String version_sha = stpJapi.get_git_version_sha();
    System.out.println("\nSHA of this STP version is :");
    System.out.println(version_sha);

    String version_tag = stpJapi.get_git_version_tag();
    System.out.println("\nThis STP version is :");
    System.out.println(version_tag);

  }

  @Test
  public void testStpCompilationEnvironment() throws Exception {
    String compile_env = stpJapi.get_compilation_env();
    System.out.println("\nCompilation Environment of this STP version is :");

    System.out.println(compile_env);

    // stpJapi.
    ifaceflag_t x = ifaceflag_t.EXPRDELETE;
  }

}

