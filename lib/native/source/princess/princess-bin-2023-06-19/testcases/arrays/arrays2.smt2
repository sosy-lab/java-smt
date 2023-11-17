(set-logic AUFLIA)

(declare-fun arr () (Array Int Int Int))

(assert (= (store arr 1 3 2) arr))
(assert (not (= (select arr 1 3) 2)))

(check-sat)
(exit)
