

(declare-const x Real)

(assert (not (exists ((y Real)) (> y x))))

(check-sat)
