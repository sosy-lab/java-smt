(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)

(assert (= x "\f"))
(assert (= y "\t"))

(assert (not (= x y)))
(check-sat)
