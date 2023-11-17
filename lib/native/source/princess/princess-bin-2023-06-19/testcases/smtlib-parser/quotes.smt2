(set-logic AUFLIA)

(declare-fun x () Int)
(assert (not (= x |x|)))

(check-sat)
(exit)
