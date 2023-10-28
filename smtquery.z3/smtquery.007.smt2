(declare-fun |id#0@1| () (_ BitVec 32))
(assert (and (bvsle #x00000000 |id#0@1|) (bvsle |id#0@1| #x0000000a)))
(check-sat)
