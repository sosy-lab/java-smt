(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)

(assert (= x "\x48\145\x6cl"))
(assert (= y "\u{48}e\u6cl"))

(assert (not (= x y)))
(check-sat)
