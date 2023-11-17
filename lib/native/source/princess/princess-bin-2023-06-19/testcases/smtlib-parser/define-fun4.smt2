
(set-option :inline-size-limit 0)

(declare-const y Int)
(declare-fun f (Int) Int)
(define-fun inc ((x Int)) Int (+ x 1))

(assert (= (f 42) (inc y)))

(check-sat)
(get-model)

