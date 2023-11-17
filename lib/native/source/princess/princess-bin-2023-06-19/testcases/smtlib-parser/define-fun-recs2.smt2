
(set-logic AUFLIA)

(define-funs-rec ((f1 ((x Int)) Int)
                  (f2 ((x Int)) Int)) (
    (ite (> x 0) (* 2 (f2 (- x 1))) 1)
    (+ 1 (f1 x))
  ))

(declare-const c Int)

(assert (= (f1 3) c))

(check-sat)
(get-value (c))
