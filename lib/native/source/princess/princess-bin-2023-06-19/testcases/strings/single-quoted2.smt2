(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)

(assert (= x ''''))
(assert (= y "'"))

(assert (not (= x y)))
(check-sat)
