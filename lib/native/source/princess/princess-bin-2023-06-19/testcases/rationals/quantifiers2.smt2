

(declare-const x Real)

(assert (not (exists ((y Real)) 
   (and (> y x) (< y (+ x 1.0))))))

(check-sat)
