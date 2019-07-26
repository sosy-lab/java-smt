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

//import org.sosy_lab.java_smt.solvers.stp.
//import org.sosy_lab.java_smt.native_api.stp.Type;

public class StpNativeApi {

  static String getStpVersion() {
    return org.sosy_lab.java_smt.solvers.stp.StpJavaApi.get_git_version_tag();
  }


  static long getStpBoolType(StpSolverContext context) throws Exception {
    VC vc = context.getFormulaCreator().getVC();
    return Type.getCPtr(org.sosy_lab.java_smt.solvers.stp.StpJavaApi.vc_boolType(vc));
  }

}
