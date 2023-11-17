; Example that previously led to the error
; "Value too big to be converted to int"

(declare-fun x () (_ BitVec 128))
(declare-fun y () (_ BitVec 128))
(declare-fun x2 () (_ BitVec 128))
(declare-fun y2 () (_ BitVec 128))

(assert (= y (bvashr x (_ bv100000000000000 128))))
(assert (bvsgt x (_ bv0 128)))

(assert (= y2 (bvashr x2 (_ bv100000000000000 128))))
(assert (bvslt x2 (_ bv0 128)))

(check-sat)
(get-model)
