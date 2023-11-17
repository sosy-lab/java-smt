(set-logic QF_S)

(declare-fun x () String)

(assert (= x "\\."))
(assert (= x "\u{5c}."))

(check-sat)
