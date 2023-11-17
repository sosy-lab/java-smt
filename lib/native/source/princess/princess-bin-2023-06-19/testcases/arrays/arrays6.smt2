(set-logic AUFLIA)

(declare-fun arr () (Array Int Int))
(declare-const x Int)
(declare-const y Int)

(assert (= (store ((as const (Array Int Int)) 0) x 10) arr))
(assert (not (>= (select arr y) 0)))

(check-sat)

