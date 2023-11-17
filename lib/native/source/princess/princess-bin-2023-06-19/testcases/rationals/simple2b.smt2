(set-logic AUFLIRA)

(declare-const x Int)

(assert (= 42 (+ x (/ 1 2))))

(check-sat)
(get-model)
