
(set-logic AUFLIA)

(define-funs-rec ((f1 ((x Int)) Int)
                  (f2 ((x Int)) Int)) (
    (ite (> x 0) (* 2 (f2 (- x 1))) 1)
    (+ 1 (f1 x))
  ))

(assert (= (f1 3) 5))

(check-sat)
