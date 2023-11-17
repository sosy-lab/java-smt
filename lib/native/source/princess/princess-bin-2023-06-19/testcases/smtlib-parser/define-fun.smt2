
(set-logic AUFLIA)

(define-fun f ((x Int) (y Int)) Int (+ x y))
(define-fun g ((x Int) (y Int)) Int y)
(define-fun gt ((x Int) (y Int)) Bool (> x y))

(assert (not (and (> (f 42 3) 0)
                  (< (g 10 (- 10)) 0)
                  (forall ((x Int) (y Int)) (= (< y x) (gt x y))))))

(check-sat)
