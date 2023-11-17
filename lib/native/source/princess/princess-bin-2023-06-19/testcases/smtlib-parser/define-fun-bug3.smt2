; In this example, it previously happened that the formula
; (= b (> x 42)) was eliminated, because "b" did not occur in
; the proof goal facts, although the formula was actually still needed

(set-logic AUFLIA)

(declare-fun b () Bool)
(declare-fun x () Int)

(define-fun f2 ((y Int)) Bool (and b (< x 0)))
(define-fun f1 ((y Int)) Bool (and (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y) (f2 y)))

(assert (f1 13))
(assert (= b (> x 42)))

(check-sat)
