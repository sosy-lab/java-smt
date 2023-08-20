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

package org.sosy_lab.java_smt.utils;
import java.io.File;  // Import the File class
import java.io.FileWriter;
import java.io.IOException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

public class BooleanLogger {

  public BooleanLogger() throws IOException {
    this.createLogFile("Out.txt");
  }

  private void createLogFile(String fileName) throws IOException {
    File myObj = new File(fileName);
    FileWriter myWriter = new FileWriter("Out.txt");
    myWriter.write("(set-logic ALL)");
    myWriter.close();
  }


  public static String logMakeVariable(String pVar) {
    String out = "(declare-const " + pVar + " Bool)";
    return out;
  }

  public static String logNot(BooleanFormula pBits) {
    String out = "(not " + pBits + ")";
    return out;
  }

  public static String logOr(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(or " + pBits1 + " " + pBits2 + ")";
    return out;
  }

  public static String logAnd(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(and " + pBits1 + " " + pBits2 + ")";
    return out;
  }

}
