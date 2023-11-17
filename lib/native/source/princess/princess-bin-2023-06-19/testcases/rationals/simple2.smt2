(set-logic AUFLIRA)

(declare-const x Real)

(assert (= 42 (+ x 1)))

(check-sat)
(get-model)
