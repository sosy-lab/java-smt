
(set-logic AUFLIA)

(assert (not (and
    (forall ((x Int)) (and (= x (+ (* 5 (div x 5)) (mod x 5)))
                           (>= (mod x 5) 0)
                           (< (mod x 5) 5)))
    (forall ((x Int)) (and (= x (+ (* (- 5) (div x (- 5))) (mod x (- 5))))
                           (>= (mod x (- 5)) 0)
                           (< (mod x (- 5)) 5)))
    (= (- 1 2 3 4 5 6) (- 19))
    (forall ((x Int)) ((_ divisible 5) (+ (* 2 x) (* 3 x))))
    (forall ((x Int)) (>= (abs x) x))
)))

(check-sat)
