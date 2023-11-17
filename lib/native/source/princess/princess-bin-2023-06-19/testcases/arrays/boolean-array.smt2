(set-logic AUFLIA)

(declare-const a (Array Int Bool))

(assert (select a 42))
(check-sat)
