(set-logic HORN)


(declare-fun |inv| ( Int ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (= A 0)
      )
      (inv A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv B)
        (= A (ite (= B 9998) 1 (+ 2 B)))
      )
      (inv A)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (inv A)
        (and (not (<= A 9996)) (not (= 0 (mod A 4))))
      )
      false
    )
  )
)

(check-sat)
(exit)
