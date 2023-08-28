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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class Generator {

  static String fileName = "Out.txt";
  static StringBuilder lines = new StringBuilder();

  public Generator() throws IOException {
    this.lines.append("(set-logic ALL)\n");
  }

  public static void writeToFile(String line) throws IOException {
    File file = new File(fileName);
    FileWriter fileWriter = new FileWriter(fileName, true);
    fileWriter.write(line);
    fileWriter.close();
  }

  public static void dumpSMTLIB2() throws IOException {
    writeToFile(String.valueOf(lines));
  }

  public static void logMakeVariable(String pVar) {
    String out = "(declare-const " + pVar + " Bool)\n";
    lines.append(out);
  }

  public static void logNot(BooleanFormula pBits) {
    String out = "(not " + pBits + ")\n";
    lines.append(out);
  }

  public static void logOr(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(or " + pBits1 + " " + pBits2 + ")\n";
    lines.append(out);
  }

  public static void logAnd(BooleanFormula pBits1, BooleanFormula pBits2) {
    String out = "(and " + pBits1 + " " + pBits2 + ")\n";
    lines.append(out);
  }
}
