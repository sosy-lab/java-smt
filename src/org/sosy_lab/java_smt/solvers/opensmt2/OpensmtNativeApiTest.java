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
package org.sosy_lab.java_smt.solvers.opensmt2;

import org.junit.Assert;
import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class OpensmtNativeApiTest {

  @BeforeClass
  public static void loadOpensmt2Library() {
    try {
      NativeLibraries.loadLibrary("opensmt2Japi");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Cannot find at least one native library", e);
    }
  }

  // @Ignore
  // @BeforeClass
  // public static void loadFooBarLibrary() {
  // try {
  // NativeLibraries.loadLibrary("foobarapi");
  //
  // } catch (UnsatisfiedLinkError e) {
  // throw new AssumptionViolatedException("Cannot find FOOBAR native library", e);
  // }
  // }

  osmt_context context = null;


  // @Ignore
  @Test(expected = RuntimeException.class)
  public void getOpensmtVersion() throws Exception {
    System.out.println(opensmt2Japi.osmt_version());
    // Assert.assertEquals("2", opensmt2Japi.osmt_version());
  }

  @Ignore
  @Test
  public void createOpensmt2ApiContextForBool() throws Exception {
    osmt_logic boolQF = osmt_logic.qf_bool; // TODO: osmt_logic

    System.out.println(boolQF.swigValue());
    context = opensmt2Japi.osmt_mk_context(boolQF);
    Assert.assertNotNull(context);
  }

  @Ignore
  @Test
  public void opensmt2ApiGetBoolValue() throws Exception {
    createOpensmt2ApiContextForBool();
    osmt_expr boolVar = opensmt2Japi.osmt_mk_bool_var(context, "a");
    Assert.assertEquals(osmt_result.l_false, opensmt2Japi.osmt_get_bool(context, boolVar));

  }

  /*
   * @Test public void opensmt2ApiTrue() {assertTrue(false); }//osmt_mk_true
   *
   * @Test public void opensmt2ApiFalse() {assertTrue(false); }//osmt_mk_false
   *
   * @Test public void opensmt2ApiNot() {assertTrue(false); }//osmt_mk_not
   *
   * @Test public void opensmt2ApiAnd() {assertTrue(false); }//osmt_mk_and
   *
   * @Test public void opensmt2ApiOr() {assertTrue(false); }//osmt_mk_or
   *
   * @Test public void opensmt2ApiEquals() {assertTrue(false); }//osmt_mk_eq
   *
   * @Test public void opensmt2ApiXor() {assertTrue(false); }//osmt_mk_xor
   *
   *
   * @Test public void createOpensmt2ApiContextForInt() { osmt_logic boolQF = osmt_logic.qf_lia ; //
   * TODO: osmt_logic context = opensmt2java.osmt_mk_context(boolQF); assertNotNull(context); }
   *
   * @Test public void createOpensmt2ApiContextForReal() { osmt_logic boolQF = osmt_logic.qf_lra ;
   * // TODO: osmt_logic context = opensmt2java.osmt_mk_context(boolQF); assertNotNull(context); }
   *
   * //create bool varialble //create bool AND //create bool OR
   *
   */


}
