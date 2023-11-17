(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 4))
(declare-fun yy () (_ BitVec 3))
(assert (let ((?v_0 (concat x (_ bv0 4))) (?v_3 (concat (_ bv0 3) (bvnot y)))) (let ((?v_1 (concat ?v_3 (_ bv3 2))) (?v_2 (concat (_ bv0 3) (bvnot ((_ extract 3 2) y))))) (let ((?v_4 (bvadd x ?v_2))) (not (and (and (and (= ((_ extract 8 4) (bvadd ?v_0 ?v_1)) ?v_4) (= ((_ extract 8 4) (bvadd ?v_0 (bvadd ?v_1 (concat (_ bv0 1) (concat y (_ bv0 4)))))) (bvadd x (bvadd (concat (_ bv0 1) y) ?v_2)))) (= ((_ extract 8 4) (bvadd ?v_0 (concat (concat (_ bv0 3) (bvnot yy)) (_ bv7 3)))) (bvadd x (concat (_ bv0 3) (bvnot ((_ extract 2 1) yy)))))) (= ((_ extract 7 3) (bvadd (concat x (_ bv0 3)) (concat ?v_3 (_ bv0 1)))) ?v_4)))))))
(check-sat)
(exit)
