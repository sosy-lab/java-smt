
(declare-const x Real)
(declare-const y Real)

; (assert (not (= x (to_int (to_real x)))))

(assert (not (= (to_int (+ x y)) (+ (to_int x) (to_int y)))))

(check-sat)
(get-model)
