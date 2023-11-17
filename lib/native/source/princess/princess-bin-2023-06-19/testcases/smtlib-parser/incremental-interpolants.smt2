(set-logic AUFLIA)
(set-option :produce-interpolants true)

(declare-fun p () Bool)
(declare-fun x () Int)

(assert (=> p (> x 0)))
(assert p)

(check-sat)

(assert (< x 0))

; previously, this check-sat command led to an exception
(check-sat)

; now get interpolants ...