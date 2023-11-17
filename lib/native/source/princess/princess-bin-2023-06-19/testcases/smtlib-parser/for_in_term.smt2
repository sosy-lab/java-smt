
(set-logic AUFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun f (Bool) Int)

(assert (= (f (= a b)) a))
(assert (= a 5))

(assert (not (and (=> (= a (+ b 1)) (= (f false) 5))
                  (exists ((x Bool)) (= (f x) 5))
                  (=> (= b 6) (let ((x false)) (= (f x) 5))))))

(check-sat)
