(set-logic AUFLIA)
(define-fun p1 () Bool true)
(define-fun p2 ((x Int)) Bool (> x 0))

(assert (not (=> (p2 5) p1)))

(check-sat)
(exit)