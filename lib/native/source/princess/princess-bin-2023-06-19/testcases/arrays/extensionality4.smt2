; Example in which previously the same constructor term was computed
; as solution for variable a, b, leading to an exception

(declare-datatypes ((X 0)) (((X (ar (Array Int Int))))))

(declare-const a X)
(declare-const b X)

(assert (= (select (ar a) 1) 1))
(assert (= (select (ar a) 2) 2))

(assert (= (select (ar b) 1) 1))
(assert (= (select (ar b) 2) 2))

(check-sat)
(get-model)
