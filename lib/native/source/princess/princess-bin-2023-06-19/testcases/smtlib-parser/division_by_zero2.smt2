(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)

(declare-fun a () Int)
(assert (= (div a 0) 4))
(check-sat) ; sat!
(get-model)

(simplify (= (div a 0) 4))

(exit)