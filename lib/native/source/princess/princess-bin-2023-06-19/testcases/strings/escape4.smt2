(set-logic QF_S)

(declare-fun x () String)

(assert (= x "\."))      ; \ does not start an escape sequence here
(assert (= x "\u{5c}."))

(check-sat)
