
(set-logic AUFLIA)

(set-option :inline-definitions false)

(declare-fun c () Int)
(define-fun f ((x Int)) Int (+ x c))

(assert (forall ((x Int)) (=> (> x 0) (> (f x) 0))))
(assert (< c 0))

(check-sat)
