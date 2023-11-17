(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)

(set-option :produce-interpolants true)

(assert (! (>= (f x) 0) :named A))
(assert (! (< (f y) 0) :named B))
(assert (! (= x y) :named C))

(check-sat)
(get-interpolants A (B) C)
