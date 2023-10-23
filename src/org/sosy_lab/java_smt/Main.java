package org.sosy_lab.java_smt;/*
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

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.java_smt.api.*;
import java.io.*;
import org.sosy_lab.java_smt.utils.Parsers.*;
import org.sosy_lab.java_smt.utils.Parsers.smtlibv2Parser.StartContext;

public class Main {
  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, IOException, SolverException {

    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromString("(declare-const b (Array Int "
        + "Int)"
        + ")\n"
        + "(declare-const a (Array Int Real))\n"
        + "(assert (= a b))\n"));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));

    StartContext tree = parser.start();
    Visitor visitor = new Visitor();
    visitor.visit(tree);



  }
}

