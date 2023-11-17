; Try and see if concat breaks this:
; manually rewrite this to without concat and see if it works!

(declare-fun a () (_ BitVec 8))
(declare-fun dummy () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 8))
(declare-fun v4 () (_ BitVec 8))


(assert
(and
  (not (= ((_ extract 5 4) v1) ((_ extract 3 2) v1)))
  (not (= ((_ extract 5 4) v4) ((_ extract 3 2) v4)))
  (or
    (and
       (= ((_ extract 7 2) a) (concat ((_ extract 7 4) v1) dummy))
       (= ((_ extract 5 0) a) (concat dummy ((_ extract 3 0) v1)))
    )
    (and
       (= ((_ extract 7 2) a) (concat ((_ extract 7 4) v4) dummy))
       (= ((_ extract 5 0) a) (concat dummy ((_ extract 3 0) v4)))
    )
  )
)
)
(check-sat)


