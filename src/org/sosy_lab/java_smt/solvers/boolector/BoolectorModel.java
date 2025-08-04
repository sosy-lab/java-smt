// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

class BoolectorModel extends AbstractModel<Long, Long, Long> {

  private static final ImmutableSet<String> SMT_KEYWORDS =
      ImmutableSet.of(
          "let",
          "forall",
          "exists",
          "match",
          "Bool",
          "continued-execution",
          "error",
          "immediate-exit",
          "incomplete",
          "logic",
          "memout",
          "sat",
          "success",
          "theory",
          "unknown",
          "unsupported",
          "unsat",
          "_",
          "as",
          "BINARY",
          "DECIMAL",
          "HEXADECIMAL",
          "NUMERAL",
          "par",
          "STRING",
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option");

  private final long btor;
  private final BoolectorTheoremProver prover;
  private final BoolectorFormulaCreator bfCreator;
  private final ImmutableList<Long> assertedTerms;

  BoolectorModel(
      long btor,
      BoolectorFormulaCreator creator,
      BoolectorTheoremProver pProver,
      Collection<Long> assertedTerms) {
    super(pProver, creator);
    this.bfCreator = creator;
    this.btor = btor;
    this.prover = pProver;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Override
  public void close() {
    if (!isClosed()) {
      // TODO Technically Boolector has no model, but you could release all bindings.
    }
    super.close();
  }

  /* (non-Javadoc)
  * Escape characters are used if the string contains i.e. spaces or ( ).
  * If one wants to use |, one needs an escape char, either | or \

  * Get String representation for each asserted term
  * Search each string for variables/ufs/arrays and gather them by using the vars cache

  * Split of () at the beginning and end, get substrings by spaces if no | is present, get
  * substrings encasing | | without escape chars else then by spacing
  * (\|.+?\|(?<!\\\|))|

  * It might be that Boolector uses "BTOR_1@varname" or BTORanyNumber@ (their own BTOR format)
  * for some reason as an escape for vars! We set the proper option that it should always
  * return smt2, but ok.
  * There is some number before the @, the varname is after the @
  * There is no further escape in this case, so a var named "@a" will be returned as
  * "BTOR_2@@a"
  * It might occur that it is double escaped, with smt2 escape and btor escape, example:
  * |BTOR_22@bla|
  * Further, it might be that Boolector returns the variable name with its own escape added, so
  * we have to strip this if it occurs
  */
  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    // Use String instead of the node (long) as we need the name again later!
    ImmutableSet.Builder<String> variablesBuilder = ImmutableSet.builder();

    for (long term : assertedTerms) {
      String termString = BtorJNI.boolector_help_dump_node_smt2(btor, term);

      List<String> escapedList = new ArrayList<>();
      // Matches all escaped names
      Pattern pattern = Pattern.compile("(\\|.+?\\|(?<!\\\\\\|))");
      Matcher matcher = pattern.matcher(termString);

      while (matcher.find()) {
        escapedList.add(matcher.group());
      }
      // Now remove all escaped strings from the term string as it allows
      // special characters/keywords
      String inputReplaced = termString;
      for (String escaped : escapedList) {
        inputReplaced = inputReplaced.replace(escaped, "");
      }
      // Delete brackets, but keep the spaces, then split on spaces into substrings
      inputReplaced = inputReplaced.replace("(", " ").replace(")", " ");
      Iterable<String> maybeVars = Splitter.onPattern("\\s+").split(inputReplaced);
      // maybeVars may include a lot of unnecessary Strings, including SMT keywords or empty
      // strings. However, removing them would just increase runtime with no benefit as we check
      // them against the variables cache.
      // TODO: decide if its benefitial to code cleanness and structure to handle the strings
      // proper, or else remove the SMT_KEYWORDS

      // Strings in maybeVars may not have SMTLIB2 keywords
      for (String var : maybeVars) {
        // Strip Boolector escape sequence (BTOR_number@; example: BTOR_1@)
        // It seems like that if the escape seq is used as a name, there will be an escape seq
        // before it. Always only removing the first should be fine
        String varReplaced = var.replaceFirst("^(BTOR_\\d+@)", "");

        if (!SMT_KEYWORDS.contains(varReplaced) && bfCreator.formulaCacheContains(varReplaced)) {
          variablesBuilder.add(varReplaced);
        }
      }
      // escaped Strings may have SMTLIB2 keywords in them
      for (String var : escapedList) {
        // Get rid of the sourrounding | and strip Boolector escape sequence (BTOR_number@; example:
        // BTOR_1@) if present
        String varSubs = var.substring(1, var.length() - 1).replaceFirst("^(BTOR_\\d+@)", "");

        if (bfCreator.formulaCacheContains(varSubs)) {
          variablesBuilder.add(varSubs);
        }
      }
    }
    return toList1(variablesBuilder.build());
  }

  private ImmutableList<ValueAssignment> toList1(Set<String> variables) {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignmentBuilder = ImmutableList.builder();
    for (String name : variables) {
      // We get the formula here as we need the name.
      // Reason: Boolector returns names of variables with its own escape sequence sometimes. If you
      // however name your variable like the escape sequence, we can't discern anymore if it's a
      // real
      // name or an escape seq.
      long entry = bfCreator.getFormulaFromCache(name).orElseThrow();
      if (BtorJNI.boolector_is_array(btor, entry)) {
        assignmentBuilder.add(getArrayAssignment(entry, name));
      } else if (BtorJNI.boolector_is_const(btor, entry)) {
        // Don't remove this! Some consts are Ufs in the eyes of Boolector, however,
        // we want them as consts!
        assignmentBuilder.add(getConstAssignment(entry, name));
      } else if (BtorJNI.boolector_is_uf(btor, entry)) {
        assignmentBuilder.addAll(getUFAssignments(entry, name));
      } else {
        // This is the Bv case
        assignmentBuilder.add(getConstAssignment(entry, name));
      }
    }
    return assignmentBuilder.build();
  }

  private ValueAssignment getConstAssignment(long key, String name) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Object value = creator.convertValue(key, evalImpl(key));
    long valueNode = BtorJNI.boolector_get_value(btor, key);
    // Boolector might return the internal name of the variable with a leading BTOR_number@ which we
    // need to strip!
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, valueNode)),
        name,
        value,
        argumentInterpretation);
  }

  private ImmutableList<ValueAssignment> getUFAssignments(long key, String name) {
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    // Don't use the creator with convertValue() as while it returns the correct values, the order
    // of values may differ when calling boolector_uf_assignment_helper again to get the arguments!
    // The "value" from boolector_get_value() is just
    // a plain copy of the entered node with static results!
    long fun = BtorJNI.boolector_get_value(btor, key);
    String[][] ufAssignments = BtorJNI.boolector_uf_assignment_helper(btor, key);
    for (int i = 0; i < ufAssignments[0].length; i++) {
      ImmutableList.Builder<Object> argBuilder = ImmutableList.builder();
      String arguments = ufAssignments[0][i];
      Object value = bfCreator.transformStringToBigInt(ufAssignments[1][i]);
      for (String arg : Splitter.onPattern("\\s+").splitToList(arguments)) {
        argBuilder.add(bfCreator.transformStringToBigInt(arg));
      }
      Long equality = BtorJNI.boolector_eq(btor, key, fun);
      // Boolector might return the internal name of the variable with a leading BTOR_number@ which
      // we need to strip!
      assignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(key),
              creator.encapsulateWithTypeOf(fun),
              creator.encapsulateBoolean(equality),
              name,
              value,
              argBuilder.build()));
    }
    return assignments.build();
  }

  private ValueAssignment getArrayAssignment(long key, String name) {
    // Don't use the creator with convertValue() as while it returns the correct values, the order
    // of values may differ when calling boolector_array_assignment_helper again to get the
    // arguments!
    List<Object> argumentInterpretation = new ArrayList<>();
    for (String stringArrayEntry : BtorJNI.boolector_array_assignment_helper(btor, key)[0]) {
      argumentInterpretation.add(bfCreator.transformStringToBigInt(stringArrayEntry));
    }
    Object value = creator.convertValue(key, evalImpl(key));
    long valueNode = BtorJNI.boolector_get_value(btor, key);
    // Boolector might return the internal name of the variable with a leading BTOR_number@ which we
    // need to strip!
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, valueNode)),
        name,
        value,
        argumentInterpretation);
  }

  @Override
  protected Long evalImpl(Long pFormula) {
    Preconditions.checkState(!isClosed());
    return pFormula;
  }
}
