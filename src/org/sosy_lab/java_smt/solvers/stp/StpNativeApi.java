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
import org.sosy_lab.java_smt.native_api.stp.VC;
import org.sosy_lab.java_smt.native_api.stp.stpJapi;

public class StpNativeApi {

  static String getStpVersion() {
    return stpJapi.get_git_version_tag();
  }


  static long getStpBoolType(StpSolverContext context) throws Exception {
    // ToDo: IMPLEMENT

    // So everything needs to start with the SolverContext

    // Create a SolverContext that will manage the life span of the VC object
    // ...
    // ...
    // In this method I want to get a VC object (i.e. a SolverContext) and return
    // the address of the boolType for that context
    VC vc = null;
    // Type type = stpJapi.vc_boolType(vc);
    return StpType.getTypePtr(stpJapi.vc_boolType(vc));
  }

}
