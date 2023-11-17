(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)

(declare-fun a () Int)
(assert (= (/ a 0) 4))

(check-sat)
(exit)