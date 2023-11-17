(set-logic QF_S)

(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (not (= x "")))
(assert (= z (str.++ y x)))

(check-sat)