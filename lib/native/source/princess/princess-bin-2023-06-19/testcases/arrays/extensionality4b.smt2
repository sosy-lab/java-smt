; Example in which previously a model was computed in which the
; default values of arrays b, c were inconsistent

(declare-datatypes ((X 0)) (((X (ar (Array Int Int))))))

(declare-const a X)
(declare-const b X)
(declare-const c X)

(assert (= (select (ar a) 1) 1))
(assert (= (select (ar a) 2) 2))

(assert (= (select (ar b) 1) 1))
(assert (= (select (ar b) 2) 2))

(assert (= (store (ar b) 3 3) (ar c)))

(check-sat)
(get-model)
