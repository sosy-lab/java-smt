(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (> x y) (> y 50)))

(check-sat)
(get-model)
