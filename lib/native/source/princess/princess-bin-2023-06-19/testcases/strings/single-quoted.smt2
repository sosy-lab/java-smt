(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)

(assert (= x '\u{48}'))
(assert (= y "\u{5c}u{48}"))

(assert (not (= x y)))
(check-sat)
