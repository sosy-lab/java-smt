
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 6))

(set-option :produce-interpolants true)

(assert (and (= ((_ extract 5 0) x) z)
             (= ((_ extract 5 2) z) (_ bv11 4))))
(assert (and (= ((_ extract 7 2) y) (_ bv6 6))
             (= x y)))

(check-sat)
(get-interpolants)
