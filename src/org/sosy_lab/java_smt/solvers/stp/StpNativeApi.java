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

//TODO (LATER) use the class to extend StpJavaApi and override funct and give docs
// remove the annoying vc_isBool() from the API, if such functionality is need implement here
// 3. if multiple Type objects are allowed - change "get..." to "create.." otw -> private fields
// 4.
public class StpNativeApi {

  private static final VC vc = StpJavaApi.vc_createValidityChecker();

  static String getStpVersion() {
    return org.sosy_lab.java_smt.solvers.stp.StpJavaApi.get_git_version_tag();
  }

  static VC getStpContextVC() {
    return vc;
  }

  static long getStpBoolTypePtr() throws Exception {
    return Type.getCPtr(StpJavaApi.vc_boolType(vc));
  }

  static Type getStpBoolType(StpSolverContext context) throws Exception {
    // VC vc = context.getFormulaCreator().getVC();
    return StpJavaApi.vc_boolType(vc);
  }

  static Type getStp32bitsBitVectorType() {
    return StpJavaApi.vc_bv32Type(vc);
  }

  static Type getStpBitVectorType(int bitSize) {
    return StpJavaApi.vc_bvType(vc, bitSize);
  }

  static Type getStpArrayType() {
    // Long pIndexType, Long pElementType

    // Type x;
    // long y = x.

    // get the Types from their addresses - check native for this ?
    // confirm they are BV
    // then :
    // StpJavaApi.vc_arrayType
    return StpJavaApi.vc_bv32Type(vc);
  }
}
