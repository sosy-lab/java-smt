// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

class SynchronizedStringFormulaManager implements StringFormulaManager {

  private final StringFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedStringFormulaManager(StringFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public StringFormula makeString(String value) {
    synchronized (sync) {
      return delegate.makeString(value);
    }
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pVar);
    }
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.equal(str1, str2);
    }
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.greaterThan(str1, str2);
    }
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.greaterOrEquals(str1, str2);
    }
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.lessThan(str1, str2);
    }
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.lessOrEquals(str1, str2);
    }
  }

  @Override
  public NumeralFormula.IntegerFormula length(StringFormula str) {
    synchronized (sync) {
      return delegate.length(str);
    }
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    synchronized (sync) {
      return delegate.concat(parts);
    }
  }

  @Override
  public BooleanFormula prefix(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.prefix(str1, str2);
    }
  }

  @Override
  public BooleanFormula suffix(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.suffix(str1, str2);
    }
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    synchronized (sync) {
      return delegate.contains(str, part);
    }
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    synchronized (sync) {
      return delegate.indexOf(str, part, startIndex);
    }
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    synchronized (sync) {
      return delegate.charAt(str, index);
    }
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    synchronized (sync) {
      return delegate.substring(str, index, length);
    }
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    synchronized (sync) {
      return delegate.replace(fullStr, target, replacement);
    }
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    synchronized (sync) {
      return delegate.replaceAll(fullStr, target, replacement);
    }
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    synchronized (sync) {
      return delegate.in(str, regex);
    }
  }

  @Override
  public RegexFormula makeRegex(String value) {
    synchronized (sync) {
      return delegate.makeRegex(value);
    }
  }

  @Override
  public RegexFormula none() {
    synchronized (sync) {
      return delegate.none();
    }
  }

  @Override
  public RegexFormula all() {
    synchronized (sync) {
      return delegate.all();
    }
  }

  @Override
  public RegexFormula allChar() {
    synchronized (sync) {
      return delegate.allChar();
    }
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    synchronized (sync) {
      return delegate.range(start, end);
    }
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    synchronized (sync) {
      return delegate.concatRegex(parts);
    }
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    synchronized (sync) {
      return delegate.union(regex1, regex2);
    }
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    synchronized (sync) {
      return delegate.intersection(regex1, regex2);
    }
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    synchronized (sync) {
      return delegate.closure(regex);
    }
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    synchronized (sync) {
      return delegate.complement(regex);
    }
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    synchronized (sync) {
      return delegate.difference(regex1, regex2);
    }
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    synchronized (sync) {
      return delegate.cross(regex);
    }
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    synchronized (sync) {
      return delegate.optional(regex);
    }
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    synchronized (sync) {
      return delegate.times(regex, repetitions);
    }
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    synchronized (sync) {
      return delegate.toIntegerFormula(str);
    }
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    synchronized (sync) {
      return delegate.toStringFormula(number);
    }
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    synchronized (sync) {
      return delegate.toCodePoint(str);
    }
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codepoint) {
    synchronized (sync) {
      return delegate.fromCodePoint(codepoint);
    }
  }
}
