; Example that previously led to an exception in ExtArray.augmentModelTermSet:
; Failed to reconstruct array model

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (= b (store a 42 0)))
(assert (= 0 (select a 1)))

(check-sat)
(get-model)
