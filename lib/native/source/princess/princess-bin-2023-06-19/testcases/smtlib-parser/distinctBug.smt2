(set-option :produce-models true)
(set-option :produce-interpolants false)
(set-logic AUFNIRA)
(set-info :source |
    SMT script generated on 2015/04/25 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(declare-fun |c_old(a)| () (Array Int Bool))
(declare-fun |c_old(a)_primed| () (Array Int Bool))
(declare-fun c_a () (Array Int Bool))
(declare-fun c_a_primed () (Array Int Bool))
(declare-fun |c_old(x)| () Int)
(declare-fun |c_old(x)_primed| () Int)
(declare-fun c_x () Int)
(declare-fun c_x_primed () Int)
(declare-fun v_a_7_const_-1616268193 () (Array Int Bool))
(assert (let ((v_a_7 v_a_7_const_-1616268193)) 

   (distinct (= (select v_a_7 0) true) (select v_a_7 0))
;   (not (= (select v_a_7 0) (select v_a_7 0)))

))
(check-sat)
