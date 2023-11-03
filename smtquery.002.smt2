(declare-fun |id#2@1| () (_ BitVec 32))
(assert (and (bvsle |id#2@1| #x0000000a) (bvslt |id#2@1| #x00000000)))
(check-sat)
