/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.parser;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;

public class Predefined {
  private final FormulaManager mgr;

  public Predefined(FormulaManager pManager) {
    mgr = pManager;
  }

  private <T> T foldr1(BinaryOperator<T> f, List<T> list) {
    var acc = list.get(list.size() - 1);
    for (var term : Lists.reverse(list.subList(0, list.size() - 1))) {
      acc = f.apply(term, acc);
    }
    return acc;
  }

  private <T> T foldl1(BinaryOperator<T> f, List<T> list) {
    return foldr1(f, Lists.reverse(list));
  }

  private <T extends Formula> BooleanFormula chain(
      BiFunction<T, T, BooleanFormula> f, List<T> list) {
    ImmutableList.Builder<BooleanFormula> terms = ImmutableList.builder();
    var last = list.get(0);
    for (int i = 1; i < list.size(); i++) {
      var curr = list.get(i);
      terms.add(f.apply(last, curr));
      last = curr;
    }
    return foldl1((term, acc) -> mgr.getBooleanFormulaManager().and(term, acc), terms.build());
  }

  private FormulaType<?> calculateReturnType(List<Formula> list) {
    return list.stream().anyMatch(p -> p instanceof NumeralFormula.RationalFormula)
        ? FormulaType.RationalType
        : FormulaType.IntegerType;
  }

  @SuppressWarnings({"unchecked", "rawtypes"})
  public Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> addTheorySymbols() {
    ImmutableMap.Builder<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
        predefined = ImmutableMap.builder();

    // Core
    predefined.put(
        "true",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getBooleanFormulaManager().makeTrue();
          };
        });
    predefined.put(
        "false",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getBooleanFormulaManager().makeFalse();
          };
        });
    predefined.put(
        "not",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBooleanFormulaManager().not((BooleanFormula) p.get(0));
          };
        });
    predefined.put(
        "=>",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldr1(
                (term, acc) ->
                    mgr.getBooleanFormulaManager()
                        .implication((BooleanFormula) term, (BooleanFormula) acc),
                p);
          };
        });
    predefined.put(
        "and",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (term, acc) ->
                    mgr.getBooleanFormulaManager().and((BooleanFormula) term, (BooleanFormula) acc),
                p);
          };
        });
    predefined.put(
        "or",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (term, acc) ->
                    mgr.getBooleanFormulaManager().or((BooleanFormula) term, (BooleanFormula) acc),
                p);
          };
        });
    predefined.put(
        "xor",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (term, acc) ->
                    mgr.getBooleanFormulaManager().xor((BooleanFormula) term, (BooleanFormula) acc),
                p);
          };
        });
    predefined.put(
        "=",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return mgr.equal(p);
          };
        });
    predefined.put(
        "distinct",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return mgr.distinct(p);
          };
        });
    predefined.put(
        "ite",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getBooleanFormulaManager()
                .ifThenElse((BooleanFormula) p.get(0), p.get(1), p.get(2));
          };
        });

    // Reals + Ints
    predefined.put(
        "-",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 1);
            if (p.size() == 1) {
              if (p.get(0) instanceof NumeralFormula.IntegerFormula) {
                return mgr.getIntegerFormulaManager()
                    .negate((NumeralFormula.IntegerFormula) p.get(0));
              } else {
                return mgr.getRationalFormulaManager()
                    .negate((NumeralFormula.RationalFormula) p.get(0));
              }
            } else {
              if (calculateReturnType(p).isIntegerType()) {
                return foldl1(
                    (a, b) ->
                        mgr.getIntegerFormulaManager()
                            .subtract(
                                (NumeralFormula.IntegerFormula) a,
                                (NumeralFormula.IntegerFormula) b),
                    p);
              } else {
                return foldl1(
                    (a, b) ->
                        mgr.getRationalFormulaManager()
                            .subtract((NumeralFormula) a, (NumeralFormula) b),
                    p);
              }
            }
          };
        });
    predefined.put(
        "+",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return foldl1(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .add(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return foldl1(
                  (a, b) ->
                      mgr.getRationalFormulaManager().add((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        "*",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return foldl1(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .multiply(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return foldl1(
                  (a, b) ->
                      mgr.getRationalFormulaManager()
                          .multiply((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        "/",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getRationalFormulaManager().divide((NumeralFormula) a, (NumeralFormula) b),
                p);
          };
        });
    predefined.put(
        "div",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getIntegerFormulaManager()
                        .divide(
                            (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                p);
          };
        });
    predefined.put(
        "mod",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getIntegerFormulaManager()
                .modulo(
                    (NumeralFormula.IntegerFormula) p.get(0),
                    (NumeralFormula.IntegerFormula) p.get(1));
          };
        });
    predefined.put(
        "abs",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            var term = (NumeralFormula.IntegerFormula) p.get(0);
            var zero = mgr.getIntegerFormulaManager().makeNumber(0);
            return mgr.getBooleanFormulaManager()
                .ifThenElse(
                    mgr.getIntegerFormulaManager().greaterOrEquals(term, zero),
                    term,
                    mgr.getIntegerFormulaManager().negate(term));
          };
        });
    predefined.put(
        "<=",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return chain(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .lessOrEquals(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return chain(
                  (a, b) ->
                      mgr.getRationalFormulaManager()
                          .lessOrEquals((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        "<",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return chain(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .lessThan(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return chain(
                  (a, b) ->
                      mgr.getRationalFormulaManager()
                          .lessThan((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        ">=",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return chain(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .greaterOrEquals(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return chain(
                  (a, b) ->
                      mgr.getRationalFormulaManager()
                          .greaterOrEquals((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        ">",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            if (calculateReturnType(p).isIntegerType()) {
              return chain(
                  (a, b) ->
                      mgr.getIntegerFormulaManager()
                          .greaterThan(
                              (NumeralFormula.IntegerFormula) a, (NumeralFormula.IntegerFormula) b),
                  p);
            } else {
              return chain(
                  (a, b) ->
                      mgr.getRationalFormulaManager()
                          .greaterThan((NumeralFormula) a, (NumeralFormula) b),
                  p);
            }
          };
        });
    predefined.put(
        "to_real",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            Preconditions.checkArgument(p.get(0) instanceof NumeralFormula.IntegerFormula);
            return mgr.getRationalFormulaManager().sum(ImmutableList.of((NumeralFormula) p.get(0)));
          };
        });
    predefined.put(
        "to_int",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            Preconditions.checkArgument(p.get(0) instanceof NumeralFormula.RationalFormula);
            return mgr.getRationalFormulaManager().floor((NumeralFormula) p.get(0));
          };
        });
    predefined.put(
        "is_int",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            Preconditions.checkArgument(p.get(0) instanceof NumeralFormula.RationalFormula);
            return mgr.equal(
                mgr.getRationalFormulaManager()
                    .sum(
                        ImmutableList.of(
                            mgr.getRationalFormulaManager().floor((NumeralFormula) p.get(0)))),
                p.get(0));
          };
        });

    // Bitvectors
    predefined.put(
        "bvnot",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager().not((BitvectorFormula) p.get(0));
          };
        });
    predefined.put(
        "bvand",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .and((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "bvor",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager().or((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "bvxor",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .xor((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "concat",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .concat((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "extract",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .extract((BitvectorFormula) p.get(0), idx.get(0), idx.get(1));
          };
        });
    predefined.put(
        "sign_extend",
        idx -> {
          Preconditions.checkArgument(idx.size() == 1);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .extend((BitvectorFormula) p.get(0), idx.get(0), true);
          };
        });
    predefined.put(
        "zero_extend",
        idx -> {
          Preconditions.checkArgument(idx.size() == 1);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .extend((BitvectorFormula) p.get(0), idx.get(0), true);
          };
        });
    predefined.put(
        "bvshl",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .shiftLeft((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1));
          };
        });
    predefined.put(
        "bvashr",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .shiftRight((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvlshr",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .shiftRight((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "rotate_left",
        idx -> {
          Preconditions.checkArgument(idx.size() == 1);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .rotateLeft((BitvectorFormula) p.get(0), idx.get(0));
          };
        });
    predefined.put(
        "rotate_right",
        idx -> {
          Preconditions.checkArgument(idx.size() == 1);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .rotateRight((BitvectorFormula) p.get(0), idx.get(0));
          };
        });
    predefined.put(
        "bvneg",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager().negate((BitvectorFormula) p.get(0));
          };
        });
    predefined.put(
        "bvadd",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .add((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "bvsub",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .subtract((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "bvmul",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return foldl1(
                (a, b) ->
                    mgr.getBitvectorFormulaManager()
                        .multiply((BitvectorFormula) a, (BitvectorFormula) b),
                p);
          };
        });
    predefined.put(
        "bvsdiv",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .divide((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvudiv",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .divide((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "bvsmod",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .smodulo((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1));
          };
        });
    predefined.put(
        "bvsrem",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .remainder((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvurem",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .remainder((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvsge",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .greaterOrEquals((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvuge",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .greaterOrEquals((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "bvsgt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .greaterThan((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvugt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .greaterThan((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "bvsle",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .lessOrEquals((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvule",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .lessOrEquals((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "bvslt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .lessThan((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), true);
          };
        });
    predefined.put(
        "bvult",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getBitvectorFormulaManager()
                .lessThan((BitvectorFormula) p.get(0), (BitvectorFormula) p.get(1), false);
          };
        });
    predefined.put(
        "int_to_bv",
        idx -> {
          Preconditions.checkArgument(idx.size() == 1);
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .makeBitvector(idx.get(0), (NumeralFormula.IntegerFormula) p.get(0));
          };
        });
    predefined.put(
        "sbt_to_int",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .toIntegerFormula((BitvectorFormula) p.get(0), true);
          };
        });
    predefined.put(
        "ubt_to_int",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getBitvectorFormulaManager()
                .toIntegerFormula((BitvectorFormula) p.get(0), false);
          };
        });

    // Floats
    Function<List<Integer>, Function<List<Formula>, Formula>> rne =
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeRoundingMode(FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
          };
        };
    predefined.put("roundNearestTiesToEven", rne);
    predefined.put("RNE", rne);
    Function<List<Integer>, Function<List<Formula>, Formula>> rna =
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeRoundingMode(FloatingPointRoundingMode.NEAREST_TIES_AWAY);
          };
        };
    predefined.put("roundNearestTiesAway", rna);
    predefined.put("RNA", rna);
    Function<List<Integer>, Function<List<Formula>, Formula>> rtp =
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeRoundingMode(FloatingPointRoundingMode.TOWARD_POSITIVE);
          };
        };
    predefined.put("roundTowardsPositive", rtp);
    predefined.put("RTP", rtp);
    Function<List<Integer>, Function<List<Formula>, Formula>> rtn =
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeRoundingMode(FloatingPointRoundingMode.TOWARD_NEGATIVE);
          };
        };
    predefined.put("roundTowardsNegative", rtn);
    predefined.put("RTN", rtn);
    Function<List<Integer>, Function<List<Formula>, Formula>> rtz =
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeRoundingMode(FloatingPointRoundingMode.TOWARD_ZERO);
          };
        };
    predefined.put("roundTowardsZero", rtz);
    predefined.put("RTZ", rtz);

    // TODO fp

    predefined.put(
        "+oo",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makePlusInfinity(FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
          };
        });
    predefined.put(
        "-oo",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeMinusInfinity(FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
          };
        });
    predefined.put(
        "+zero",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeNumber(0.0, FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
          };
        });
    predefined.put(
        "-zero",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeNumber(-0.0, FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
          };
        });
    predefined.put(
        "NaN",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.isEmpty());
            return mgr.getFloatingPointFormulaManager()
                .makeNaN(FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
          };
        });
    predefined.put(
        "fp.abs",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().abs((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.neg",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().negate((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.add",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getFloatingPointFormulaManager()
                .add(
                    (FloatingPointFormula) p.get(1),
                    (FloatingPointFormula) p.get(2),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.sub",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getFloatingPointFormulaManager()
                .subtract(
                    (FloatingPointFormula) p.get(1),
                    (FloatingPointFormula) p.get(2),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.mul",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getFloatingPointFormulaManager()
                .multiply(
                    (FloatingPointFormula) p.get(1),
                    (FloatingPointFormula) p.get(2),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.div",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getFloatingPointFormulaManager()
                .divide(
                    (FloatingPointFormula) p.get(1),
                    (FloatingPointFormula) p.get(2),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.fma",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            throw new UnsupportedOperationException("Fused multiply-add not supported in JavaSMT");
          };
        });
    predefined.put(
        "fp.sqrt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getFloatingPointFormulaManager()
                .sqrt(
                    (FloatingPointFormula) p.get(1),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.rem",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getFloatingPointFormulaManager()
                .remainder((FloatingPointFormula) p.get(0), (FloatingPointFormula) p.get(1));
          };
        });
    predefined.put(
        "fp.roundToIntegral",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getFloatingPointFormulaManager()
                .round(
                    (FloatingPointFormula) p.get(1),
                    mgr.getFloatingPointFormulaManager()
                        .fromRoundingModeFormula((FloatingPointRoundingModeFormula) p.get(0)));
          };
        });
    predefined.put(
        "fp.min",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getFloatingPointFormulaManager()
                .min((FloatingPointFormula) p.get(0), (FloatingPointFormula) p.get(1));
          };
        });
    predefined.put(
        "fp.max",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getFloatingPointFormulaManager()
                .max((FloatingPointFormula) p.get(0), (FloatingPointFormula) p.get(1));
          };
        });
    predefined.put(
        "fp.leq",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return chain(
                (a, b) ->
                    mgr.getFloatingPointFormulaManager()
                        .lessOrEquals((FloatingPointFormula) a, (FloatingPointFormula) b),
                p);
          };
        });
    predefined.put(
        "fp.lt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return chain(
                (a, b) ->
                    mgr.getFloatingPointFormulaManager()
                        .lessThan((FloatingPointFormula) a, (FloatingPointFormula) b),
                p);
          };
        });
    predefined.put(
        "fp.geq",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return chain(
                (a, b) ->
                    mgr.getFloatingPointFormulaManager()
                        .greaterOrEquals((FloatingPointFormula) a, (FloatingPointFormula) b),
                p);
          };
        });
    predefined.put(
        "fp.gt",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return chain(
                (a, b) ->
                    mgr.getFloatingPointFormulaManager()
                        .greaterThan((FloatingPointFormula) a, (FloatingPointFormula) b),
                p);
          };
        });
    predefined.put(
        "fp.eq",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() >= 2);
            return chain(
                (a, b) ->
                    mgr.getFloatingPointFormulaManager()
                        .equalWithFPSemantics((FloatingPointFormula) a, (FloatingPointFormula) b),
                p);
          };
        });
    predefined.put(
        "fp.isNormal",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().isNormal((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isSubnormal",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager()
                .isSubnormal((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isZero",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().isZero((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isInfinite",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().isInfinity((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isNaN",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().isNaN((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isNegative",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager().isNegative((FloatingPointFormula) p.get(0));
          };
        });
    predefined.put(
        "fp.isPositive",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            return mgr.getFloatingPointFormulaManager()
                .isNegative(
                    mgr.getFloatingPointFormulaManager().negate((FloatingPointFormula) p.get(0)));
          };
        });
    predefined.put(
        "to_fp",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.size() == 1 || p.size() == 2);
            if (p.size() == 1) {
              return mgr.getFloatingPointFormulaManager()
                  .fromIeeeBitvector(
                      (BitvectorFormula) p.get(0),
                      FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1));
            } else {
              var rm = (FloatingPointRoundingModeFormula) p.get(0);
              var from = p.get(1);
              return mgr.getFloatingPointFormulaManager()
                  .castFrom(
                      from,
                      true,
                      FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1),
                      mgr.getFloatingPointFormulaManager().fromRoundingModeFormula(rm));
            }
          };
        });
    predefined.put(
        "to_fp_unsigned",
        idx -> {
          Preconditions.checkArgument(idx.size() == 2);
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            var rm = (FloatingPointRoundingModeFormula) p.get(0);
            var from = (BitvectorFormula) p.get(1);
            return mgr.getFloatingPointFormulaManager()
                .castFrom(
                    from,
                    false,
                    FormulaType.getFloatingPointType(idx.get(0), idx.get(1) - 1),
                    mgr.getFloatingPointFormulaManager().fromRoundingModeFormula(rm));
          };
        });
    predefined.put(
        "fp.to_ubv",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            var rm = (FloatingPointRoundingModeFormula) p.get(0);
            var from = (FloatingPointFormula) p.get(1);
            var fromType = (FormulaType.FloatingPointType) mgr.getFormulaType(from);
            var toType =
                FormulaType.getBitvectorTypeWithSize(
                    1 + fromType.getExponentSize() + fromType.getMantissaSize());
            return mgr.getFloatingPointFormulaManager()
                .castTo(
                    from,
                    false,
                    toType,
                    mgr.getFloatingPointFormulaManager().fromRoundingModeFormula(rm));
          };
        });
    predefined.put(
        "fp.to_sbv",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            var rm = (FloatingPointRoundingModeFormula) p.get(0);
            var from = (FloatingPointFormula) p.get(1);
            var fromType = (FormulaType.FloatingPointType) mgr.getFormulaType(from);
            var toType =
                FormulaType.getBitvectorTypeWithSize(
                    1 + fromType.getExponentSize() + fromType.getMantissaSize());
            return mgr.getFloatingPointFormulaManager()
                .castTo(
                    from,
                    true,
                    toType,
                    mgr.getFloatingPointFormulaManager().fromRoundingModeFormula(rm));
          };
        });
    predefined.put(
        "fp.to_real",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 1);
            var from = (FloatingPointFormula) p.get(0);
            return mgr.getFloatingPointFormulaManager()
                .castTo(from, true, FormulaType.RationalType);
          };
        });

    // Arrays
    predefined.put(
        "select",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 2);
            return mgr.getArrayFormulaManager().select((ArrayFormula) p.get(0), p.get(1));
          };
        });
    predefined.put(
        "store",
        idx -> {
          Preconditions.checkArgument(idx.isEmpty());
          return p -> {
            Preconditions.checkArgument(p.size() == 3);
            return mgr.getArrayFormulaManager().store((ArrayFormula) p.get(0), p.get(1), p.get(2));
          };
        });

    return predefined.buildOrThrow();
  }
}
