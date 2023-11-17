
(set-logic AUFLIA)

(define-fun-rec square ((x Int)) Int
    (ite (> x 0) (+ (square (- x 1)) (* 2 x) (- 1)) 0))

(assert (not (>= (square 4) 0)))

(check-sat)
