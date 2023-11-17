; a and b have to be mapped to distinct arrays

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (distinct a b))

(check-sat)
(get-model)
