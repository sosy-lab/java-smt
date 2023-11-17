(set-logic AUFLIA)

(declare-const p Bool)

(assert (forall ((a Bool)) (ite p a (not a))))

(check-sat)
