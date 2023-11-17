(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun e () (_ BitVec 4))
(declare-fun f () (_ BitVec 3))
(assert
(not
(=>
    (=
       ((_ extract 7 2) (concat (concat f e) (_ bv2 3)))
       (concat f f)
    )
    (=>
       (= e (_ bv15 4))
       (= f (_ bv1 3))
    )
)
)
)
(check-sat)
(exit)
