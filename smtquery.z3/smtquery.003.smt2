(declare-fun |id#2@1| () (_ BitVec 32))
(assert (and (bvsle #x00000000 |id#2@1|) (bvsle |id#2@1| #x0000000a)))
(check-sat)
