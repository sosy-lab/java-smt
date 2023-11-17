
(declare-const x (_ BitVec 128))

(assert (not (= (_ bv0 128) (bvlshr x (_ bv999999999999 128)))))
(check-sat)