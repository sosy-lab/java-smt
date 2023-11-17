(set-logic QF_LIA)
(set-info :source |
Mathsat benchmarks available from http://mathsat.itc.it

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ARG1_LSBRCK_0_RSBRCK_ () Bool)
(declare-fun arg1_LSBRCK_0_RSBRCK_ () Int)
(declare-fun ARG1_LSBRCK_1_RSBRCK_ () Bool)
(declare-fun arg1_LSBRCK_1_RSBRCK_ () Int)
(declare-fun arg1 () Int)
(declare-fun ARG2_LSBRCK_0_RSBRCK_ () Bool)
(declare-fun arg2_LSBRCK_0_RSBRCK_ () Int)
(declare-fun ARG2_LSBRCK_1_RSBRCK_ () Bool)
(declare-fun arg2_LSBRCK_1_RSBRCK_ () Int)
(declare-fun arg2 () Int)
(declare-fun mul1 () Int)
(declare-fun mul1_sum_LSBRCK_0_RSBRCK_ () Int)
(declare-fun mul1_sum_LSBRCK_1_RSBRCK_ () Int)
(declare-fun mul1_sum () Int)
(declare-fun mul2 () Int)
(declare-fun mul2_sum_LSBRCK_0_RSBRCK_ () Int)
(declare-fun mul2_sum_LSBRCK_1_RSBRCK_ () Int)
(declare-fun mul2_sum () Int)
(assert 

(let ((?v_0 (not ARG2_LSBRCK_0_RSBRCK_))
      (?v_1 (not ARG2_LSBRCK_1_RSBRCK_))
      (?v_2 (not ARG1_LSBRCK_0_RSBRCK_)) 
      (?v_3 (not ARG1_LSBRCK_1_RSBRCK_)))
 
 (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= arg2 0) (<= arg2 3)) (= (- (- arg2 arg2_LSBRCK_0_RSBRCK_) (* 2 arg2_LSBRCK_1_RSBRCK_)) 0)) (>= arg2_LSBRCK_0_RSBRCK_ 0)) (<= arg2_LSBRCK_0_RSBRCK_ 1)) (or ?v_0 (= arg2_LSBRCK_0_RSBRCK_ 1))) (or ARG2_LSBRCK_0_RSBRCK_ (= arg2_LSBRCK_0_RSBRCK_ 0))) (>= arg2_LSBRCK_1_RSBRCK_ 0)) (<= arg2_LSBRCK_1_RSBRCK_ 1)) (or ?v_1 (= arg2_LSBRCK_1_RSBRCK_ 1))) (or ARG2_LSBRCK_1_RSBRCK_ (= arg2_LSBRCK_1_RSBRCK_ 0))) (>= mul1_sum_LSBRCK_0_RSBRCK_ 0)) (<= mul1_sum_LSBRCK_0_RSBRCK_ 3)) (>= arg1 0)) (<= arg1 3)) (or ?v_0 (= mul1_sum_LSBRCK_0_RSBRCK_ arg1))) (or ARG2_LSBRCK_0_RSBRCK_ (= mul1_sum_LSBRCK_0_RSBRCK_ 0))) (>= mul1_sum_LSBRCK_1_RSBRCK_ 0)) (<= mul1_sum_LSBRCK_1_RSBRCK_ 3)) (or ?v_1 (= mul1_sum_LSBRCK_1_RSBRCK_ arg1))) (or ARG2_LSBRCK_1_RSBRCK_ (= mul1_sum_LSBRCK_1_RSBRCK_ 0))) (>= mul1_sum 0)) (<= mul1_sum 15)) (= (- (- mul1_sum mul1_sum_LSBRCK_0_RSBRCK_) (* 2 mul1_sum_LSBRCK_1_RSBRCK_)) 0)) (>= mul1 0)) (<= mul1 15)) (= mul1 mul1_sum)) (= (- (- arg1 arg1_LSBRCK_0_RSBRCK_) (* 2 arg1_LSBRCK_1_RSBRCK_)) 0)) (>= arg1_LSBRCK_0_RSBRCK_ 0)) (<= arg1_LSBRCK_0_RSBRCK_ 1)) (or ?v_2 (= arg1_LSBRCK_0_RSBRCK_ 1))) (or ARG1_LSBRCK_0_RSBRCK_ (= arg1_LSBRCK_0_RSBRCK_ 0))) (>= arg1_LSBRCK_1_RSBRCK_ 0)) (<= arg1_LSBRCK_1_RSBRCK_ 1)) (or ?v_3 (= arg1_LSBRCK_1_RSBRCK_ 1))) (or ARG1_LSBRCK_1_RSBRCK_ (= arg1_LSBRCK_1_RSBRCK_ 0))) (>= mul2_sum_LSBRCK_0_RSBRCK_ 0)) (<= mul2_sum_LSBRCK_0_RSBRCK_ 3)) (or ?v_2 (= mul2_sum_LSBRCK_0_RSBRCK_ arg2))) (or ARG1_LSBRCK_0_RSBRCK_ (= mul2_sum_LSBRCK_0_RSBRCK_ 0))) (>= mul2_sum_LSBRCK_1_RSBRCK_ 0)) (<= mul2_sum_LSBRCK_1_RSBRCK_ 3)) (or ?v_3 (= mul2_sum_LSBRCK_1_RSBRCK_ arg2))) (or ARG1_LSBRCK_1_RSBRCK_ (= mul2_sum_LSBRCK_1_RSBRCK_ 0))) (>= mul2_sum 0)) (<= mul2_sum 15)) (= (- (- mul2_sum mul2_sum_LSBRCK_0_RSBRCK_) (* 2 mul2_sum_LSBRCK_1_RSBRCK_)) 0)) (>= mul2 0)) (<= mul2 15)) (= mul2 mul2_sum)) (not (= mul1 mul2)))))
(check-sat)
(exit)
