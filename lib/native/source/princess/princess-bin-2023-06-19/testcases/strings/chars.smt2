(set-logic QF_)

(declare-fun x () String)
(declare-fun z () String)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)

(declare-fun ch () Int)

(assert (= (str.from_code 90) x))
(assert (= (str.from_code ch) x))
(assert (= (str.from_code (- 1)) z))
(assert (= (str.from_code (bv2nat #x73)) a))
(assert (= (str.from_code (bv2nat #x73)) b))
(assert (= (str.++ (str.from_code (bv2nat #b01110011)) (str.from_code (bv2nat #b01110100)) (str.from_code (bv2nat #b01110010)) (str.from_code (bv2nat #b01101001)) (str.from_code (bv2nat #b01101110)) (str.from_code (bv2nat #b01100111))) c))

(check-sat)
