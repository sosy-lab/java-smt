; Modeling sequential code with bitvectors
;; Correct swap with no temp var
; int x, y;
; x = x + y;
; y = x - y;
; x = x - y;

(set-logic QF_BV) 
(set-option :produce-models true)

(declare-const x_0 (_ BitVec 32))
(declare-const x_1 (_ BitVec 32))
(declare-const x_2 (_ BitVec 32))   
(declare-const y_0 (_ BitVec 32))
(declare-const y_1 (_ BitVec 32))   
(assert (= x_1 (bvadd x_0 y_0))) 
(assert (= y_1 (bvsub x_1 y_0)))
(assert (= x_2 (bvsub x_1 y_1)))

(assert (not
  (and (= x_2 y_0)
       (= y_1 x_0))))
(check-sat)
; unsat
(exit)