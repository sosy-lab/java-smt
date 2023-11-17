(set-logic AUFLIA)

(declare-const x Int)
(declare-const y Int)

(assert (= (~ x) y))
(assert (not (= x (- y))))

(check-sat)
(exit)
