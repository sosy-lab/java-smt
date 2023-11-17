(set-logic QF_S)

(declare-const x String)
(declare-const z String)

(assert (not (= x "")))
(assert (= z (str.++ x x)))

(check-sat)