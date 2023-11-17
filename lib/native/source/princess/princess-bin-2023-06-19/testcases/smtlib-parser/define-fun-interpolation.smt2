
(set-logic AUFLIA)

(set-option :produce-interpolants true)

(declare-fun c () Int)
(declare-fun d () Int)
(define-fun f ((x Int) (y Int)) Int (+ x y))

(assert (> (f c d) 0))
(assert (< (f d c) 0))

(check-sat)
(get-interpolants)
