(declare-fun |id#2@1| () (_ BitVec 32))
(declare-fun |id#0@1| () (_ BitVec 32))
(define-fun .8 () (_ BitVec 32) (_ bv0 32))
(define-fun .10 () (_ BitVec 32) (_ bv10 32))

(assert (and .10 .8))
(check-sat)
(get-model)
