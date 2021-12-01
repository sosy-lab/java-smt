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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

class BoolectorModel extends CachingAbstractModel<Long, Long, Long> {

  // TODO: The rest of the keywords any maybe make this a map for O(1) access
  private static final List<String> SMT_KEYWORDS = Arrays.asList("and", "=", "or");

  private final long btor;
  private final BoolectorAbstractProver<?> prover;
  private final BoolectorFormulaCreator bfCreator;
  private boolean closed = false;

  private final ImmutableList<Long> assertedTerms;

  BoolectorModel(
      long btor,
      BoolectorFormulaCreator creator,
      BoolectorAbstractProver<?> pProver,
      Collection<Long> assertedTerms) {
    super(creator);
    this.bfCreator = creator;
    this.btor = btor;
    this.prover = pProver;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Override
  public void close() {
    if (!closed) {
      // Technically boolector has no model,
      // but you could release all bindings.
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    HashMap<String, Long> varsCache = ((BoolectorFormulaCreator) creator).getModelMap();
    ImmutableSet.Builder<Long> variablesBuilder = ImmutableSet.builder();

    for (long term : assertedTerms) {

      // Escape characters are used if the string contains i.e. spaces or ( ).
      // If one wants to use |, one needs an escape char, either | or \

      // Get String representation for each asserted term
      // Search each string for variables/ufs/arrays and gather them by using the vars cache

      // Split of () at the beginning and end, get substrings by spaces if no | is present, get
      // substrings encasing | | without escape chars else then by spacing
      // (\|.+?\|(?<!\\\|))|

      // It might be that Boolector uses "BTOR_1@varname" or BTOR2 (their own BTOR format) for some
      // reason as an escape in this method! We set the proper option that it should always return
      // smt2, but ok.
      // The number before the @ is either 1 or 2, the varname is after the @
      // There is no further escape in this case, so a var named "@a" will be returned as
      // "BTOR_2@@a"
      // TODO: cover this case as well
      BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_OUTPUT_FORMAT.getValue(), 1);
      String termString = BtorJNI.boolector_help_dump_node_smt2(btor, term);

      System.out.println(
          "option BTOR_OPT_OUTPUT_FORMAT: "
              + BtorJNI.boolector_get_opt_lng(btor, BtorOption.BTOR_OPT_OUTPUT_FORMAT.getValue()));
      System.out.println("dump: " + termString);
      List<String> escapedList = new ArrayList<>();
      // Matches all escaped names
      Pattern pattern = Pattern.compile("(\\|.+?\\|(?<!\\\\\\|))");
      String input = termString;
      Matcher matcher = pattern.matcher(input);

      while (matcher.find()) {
        escapedList.add(matcher.group());
      }
      // Now remove all escaped strings from the term string as it allows
      // special characters/keywords
      String inputReplaced = input;
      for (String escaped : escapedList) {
        inputReplaced = inputReplaced.replace(escaped, "");
      }
      inputReplaced = inputReplaced.replace("(", " ");
      inputReplaced = inputReplaced.replace(")", " ");

      Iterable<String> maybeVars = Splitter.onPattern("\\s+").split(inputReplaced);

      // Strings in maybeVars may not have SMTLIB2 keywords
      for (String var : maybeVars) {
        if (!SMT_KEYWORDS.contains(var) && varsCache.containsKey(var)) {
          variablesBuilder.add(varsCache.get(var));
        }
      }
      // escaped Strings may have SMTLIB2 keywords in them
      for (String var : escapedList) {
        String varSubs = var.substring(1, var.length() - 1);
        if (varsCache.containsKey(varSubs)) {
          variablesBuilder.add(varsCache.get(varSubs));
        }
      }
      System.out.println(maybeVars);
      System.out.println(escapedList);
    }

    ImmutableList<ValueAssignment> assignments = toList1(variablesBuilder.build());
    return assignments;
  }

  @SuppressWarnings("unused")
  private void getVariables(String termString, Set<String> set) {
    // Cut off beginning and trailing braces
    String termStringCutBraces = termString.substring(1, termString.length() - 1);
    // Now check for | as it might mess up splitting by spaces
    // But only unescaped | are valid
    List<String> parts = Splitter.onPattern("(?<!\\\\)\\|").splitToList(termStringCutBraces);
    // Now we either split the String if a | was found, or not
    if (parts.size() > 1) {
      // If this is split into multiple parts, we know that the insides MUST be vars/ufs...

    }
  }

  @SuppressWarnings("unused")
  private ImmutableList<ValueAssignment> toList1(Set<Long> variables) {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
      for (Long entry : variables) {
        if (BtorJNI.boolector_is_array(btor, entry)) {
        System.out.println("array assignment for: " + entry);
          assignments.add(getArrayAssignment(entry));
        } else if (BtorJNI.boolector_is_const(btor, entry)) {
        System.out.println("const assignment for: " + entry);
          assignments.add(getConstAssignment(entry));
        } else if (BtorJNI.boolector_is_uf(btor, entry)) {
        System.out.println("uf assignment for: " + entry);
          assignments.addAll(getUFAssignments(entry));
      } else {
        System.out.println("bv assignment? for: " + entry);
        assignments.add(getConstAssignment(entry));
        System.out.println(getConstAssignment(entry));
        }
    }
    return assignments.build();
  }

  private ValueAssignment getConstAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Object value = creator.convertValue(key, evalImpl(key));
    Long valueNode = BtorJNI.boolector_get_value(btor, key);
    System.out.println("Uf name: " + bfCreator.getName(key));
    System.out.println("const: " + bfCreator.getName(key) + " with: " + value);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, valueNode)),
        bfCreator.getName(key),
        value,
        argumentInterpretation);
  }

  private ImmutableList<ValueAssignment> getUFAssignments(long key) {
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    // Don't use the creator with convertValue() as while it returns the correct values, the order
    // of values may differ when calling boolector_uf_assignment_helper again to get the arguments!
    // Object value = creator.convertValue(key, evalImpl(key));
    // The "value" from boolector_get_value() is just
    // a plain copy of the entered node with static results!
    Long fun = BtorJNI.boolector_get_value(btor, key);
    String[][] ufAssignments = BtorJNI.boolector_uf_assignment_helper(btor, key);
    for (int i = 0; i < ufAssignments[0].length; i++) {
      ImmutableList.Builder<Object> argBuilder = ImmutableList.builder();
      String arguments = ufAssignments[0][i];
      Object value = bfCreator.transformStringToBigInt(ufAssignments[1][i]);
      for (String arg : Splitter.onPattern("\\s+").splitToList(arguments)) {
        argBuilder.add(bfCreator.transformStringToBigInt(arg));
      }
      Long equality = BtorJNI.boolector_eq(btor, key, fun);
      System.out.println("arguments: " + argBuilder.build());
      System.out.println("value: " + value);
      assignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(key),
              creator.encapsulateWithTypeOf(fun),
              creator.encapsulateBoolean(equality),
              bfCreator.getName(key),
              value,
              argBuilder.build()));
    }
    return assignments.build();
  }

  private ValueAssignment getArrayAssignment(long key) {
    // Don't use the creator with convertValue() as while it returns the correct values, the order
    // of values may differ when calling boolector_array_assignment_helper again to get the
    // arguments!
    List<Object> argumentInterpretation = new ArrayList<>();
    for (String stringArrayEntry : BtorJNI.boolector_array_assignment_helper(btor, key)[0]) {
      argumentInterpretation.add(bfCreator.transformStringToBigInt(stringArrayEntry));
    }
    Object value = creator.convertValue(key, evalImpl(key));
    Long valueNode = BtorJNI.boolector_get_value(btor, key);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, valueNode)),
        bfCreator.getName(key),
        value,
        argumentInterpretation);
  }

  @Override
  protected Long evalImpl(Long pFormula) {
    Preconditions.checkState(!closed);
    return pFormula;
  }
}
