(set-logic AUFLIRA)

(declare-const x Real)
(declare-const y Real)

(assert (= x (+ 1 1.1)))
(assert (= (+ y 1.1) x))

(check-sat)
(get-model)
