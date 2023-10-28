(declare-fun |id#0@1| () (_ BitVec 32))
(assert (and (bvsle |id#0@1| #x0000000a) (bvslt |id#0@1| #x00000000)))
(check-sat)
