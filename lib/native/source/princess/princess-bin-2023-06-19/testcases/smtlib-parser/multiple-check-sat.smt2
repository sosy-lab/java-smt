
(set-logic AUFLIA)

(push 1)

(declare-fun f (Int) Int)

(assert (forall ((x Int)) (let ((y x)) (>= (f y) 0))))
(assert (not (>= (f 13) (- 1))))

(check-sat)
(pop 1)

(push 1)

(declare-fun f (Int) Int)

(assert (forall ((x Int)) (let ((y x)) (>= (f y) 0))))
(assert (not (>= (f 13) (- 1))))

(check-sat)
(pop 1)

(exit)
