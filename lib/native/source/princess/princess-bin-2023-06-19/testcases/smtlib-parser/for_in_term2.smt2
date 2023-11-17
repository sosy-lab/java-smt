
(set-logic AUFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun f (Bool) Int)

(assert (= (f (= a b)) a))
(assert (= a 5))

(set-option :inline-let false)

(assert (not (=> (= b 6) (let ((x false)) (= (f x) 5)))))

(check-sat)
