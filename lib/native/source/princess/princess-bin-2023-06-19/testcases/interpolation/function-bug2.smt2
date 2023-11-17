(set-option :produce-models true)
(set-option :produce-interpolants true)
(set-logic AUFLIRA)
(set-info :source |
    SMT script generated on 2015/01/30 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")

(echo "starting trace check")
;(push 1)
(declare-fun f (Int) Int)
(declare-fun upper_-1 () Int)
(declare-fun a_-1 () (Array Int Int))
(declare-fun |old(a)_-1| () (Array Int Int))
(declare-fun |old(upper)_-1| () Int)
(declare-fun ULTIMATE.start_i_-1 () Int)
(declare-fun a_0 () (Array Int Int))

(assert (and (= 23 (f upper_-1))
             (>= upper_-1 0)
             (<= ULTIMATE.start_i_-1 upper_-1)))

(assert (>= ULTIMATE.start_i_-1 (- upper_-1 1)))

(assert (not (= (f ULTIMATE.start_i_-1) 23)))
(assert (not (= (f (+ ULTIMATE.start_i_-1 1)) 23)))

(check-sat)
(echo "finished trace check")

;(pop 1)
