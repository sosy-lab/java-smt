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

package org.sosy_lab.java_smt.solvers.Solverless;

import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessStringFormulaManager extends AbstractStringFormulaManager<String, String,
    String, String> {

  protected SolverLessStringFormulaManager(FormulaCreator<String, String, String, String> pCreator) {
    super(pCreator);
  }

  @Override
  protected String makeStringImpl(String value) {
    return "";
  }

  @Override
  protected String makeVariableImpl(String pVar) {
    return "";
  }

  @Override
  protected String equal(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String greaterThan(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String greaterOrEquals(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String lessThan(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String lessOrEquals(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String length(String pParam) {
    return "";
  }

  @Override
  protected String concatImpl(List<String> parts) {
    return "";
  }

  @Override
  protected String prefix(String prefix, String str) {
    return "";
  }

  @Override
  protected String suffix(String suffix, String str) {
    return "";
  }

  @Override
  protected String in(String str, String regex) {
    return "";
  }

  @Override
  protected String contains(String str, String part) {
    return "";
  }

  @Override
  protected String indexOf(String str, String part, String startIndex) {
    return "";
  }

  @Override
  protected String charAt(String str, String index) {
    return "";
  }

  @Override
  protected String substring(String str, String index, String length) {
    return "";
  }

  @Override
  protected String replace(String fullStr, String target, String replacement) {
    return "";
  }

  @Override
  protected String replaceAll(String fullStr, String target, String replacement) {
    return "";
  }

  @Override
  protected String makeRegexImpl(String value) {
    return "";
  }

  @Override
  protected String noneImpl() {
    return "";
  }

  @Override
  protected String allImpl() {
    return "";
  }

  @Override
  protected String allCharImpl() {
    return "";
  }

  @Override
  protected String range(String start, String end) {
    return "";
  }

  @Override
  protected String concatRegexImpl(List<String> parts) {
    return "";
  }

  @Override
  protected String union(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String intersection(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String closure(String pParam) {
    return "";
  }

  @Override
  protected String complement(String pParam) {
    return "";
  }

  @Override
  protected String toIntegerFormula(String pParam) {
    return "";
  }

  @Override
  protected String toStringFormula(String pParam) {
    return "";
  }
}
