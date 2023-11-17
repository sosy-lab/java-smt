; Example that previously led to non-termination in
; ExtArray.ArraySort.augmentModelTermSet

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (= a ((as const (Array Int Int)) 1)))
(assert (= b (store a 1 1)))

(check-sat)
(get-model)

