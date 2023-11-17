
(set-logic AUFLIA)
(declare-fun a () Int)
(declare-fun f (Int) Int)

(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f x) 1))))
(assert (not (exists ((y Int)) (= (f (+ a 2)) (+ (f a) y)))))

(check-sat)
