(set-logic AUFLIA)

(set-option :produce-interpolants true)
(set-option :totality-axiom false)  ; it would work better to use the
                                    ; option -genTotalityAxioms
                                    ; (then the trigger below would not
                                    ;  have to be given manually)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))

(assert (= (store a 1 42) b))
(assert (not (exists ((x Int)) (! (> (select b x) 0)
                                  :pattern ((select b x))))))

(check-sat)
(get-interpolants)
