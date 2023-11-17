
(declare-fun f (Bool) Int)

(assert (forall ((x Bool)) (! (> (f x) 0) :pattern ((f x)))))
(assert (= (f (= 0 0)) 0))

(check-sat)