(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))

(assert (= y (bvashr x (_ bv3 16))))
(assert (bvsgt y (_ bv0 16)))
(assert (bvslt x (_ bv0 16)))

(check-sat)
