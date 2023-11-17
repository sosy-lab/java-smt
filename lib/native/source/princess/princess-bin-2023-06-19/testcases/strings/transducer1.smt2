(set-logic QF_S)

; Successor transducer

(define-funs-rec ((succ ((x String) (y String)) Bool)
                  (succH ((x String) (y String)) Bool)) (
                  ; definition of succ
                  (or (and (not (= x "")) (not (= y ""))
                           (= (str.head x) (char.from-int 48)) ; '0'
                           (= (str.head y) (char.from-int 48)) ; '0'
                           (succ (str.tail x) (str.tail y)))
                      (and (not (= x "")) (not (= y ""))
                           (= (str.head x) (char.from-int 49)) ; '1'
                           (= (str.head y) (char.from-int 49)) ; '1'
                           (succ (str.tail x) (str.tail y)))
                      (and (not (= x "")) (not (= y ""))
                           (= (str.head x) (char.from-int 48)) ; '0'
                           (= (str.head y) (char.from-int 49)) ; '1'
                           (succH (str.tail x) (str.tail y))))
                  ; definition of succH
                  (or (and (= x "")
                           (= y ""))
                      (and (not (= x "")) (not (= y ""))
                           (= (str.head x) (char.from-int 49)) ; '1'
                           (= (str.head y) (char.from-int 48)) ; '0'
                           (succH (str.tail x) (str.tail y))))))

(declare-fun x () String)
(declare-fun y () String)

; (assert (str.in.re x (re.+ (re.union (str.to.re "0") (str.to.re "1")))))
(assert (succ x y))
(assert (= (str.len x) 3))

(check-sat)