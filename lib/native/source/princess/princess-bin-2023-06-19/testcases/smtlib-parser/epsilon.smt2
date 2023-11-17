
(set-logic AUFLIA)

(declare-const x Int)
(declare-const y Int)

(assert (= 0 (_eps ((a Int)) (and (>= a 0) (or (= a x) (= a (- x)))))))
(assert (not (= x 0)))

(check-sat)