(set-logic HORN)


(declare-fun |h4| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h19| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h15| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h14| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h24| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h6| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h2| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h18| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |h1| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h8| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h13| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h12| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h10| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h23| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h7| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h17| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h16| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h3| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h9| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h11| ( Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h5| ( Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) ) 
    (=>
      (and
        (and true (= v_4 A) (= v_5 B) (= v_6 C) (= v_7 D))
      )
      (h1 A B C D v_4 v_5 v_6 v_7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (h1 A B C D E I J K)
        (and (= F 0) (= H 0) (= G 0))
      )
      (h2 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h2 A B C D E F G H)
        true
      )
      (h3 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h3 A B C D E F G H)
        true
      )
      (h4 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h4 A B C D E F G H)
        true
      )
      (h5 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h15 A B C D E F G H)
        true
      )
      (h5 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h16 A B C D E F G H)
        true
      )
      (h5 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h14 A B C D E F G H)
        true
      )
      (h5 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h5 A B C D E F G H)
        true
      )
      (h6 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h6 A B C D E F G H)
        (>= (+ E (* (- 1) H)) 1)
      )
      (h7 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (h7 A B C D E J G I)
        (and (= I (+ (- 1) H)) (= J (+ (- 1) F)))
      )
      (h8 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h6 A B C D E F G H)
        (<= (+ E (* (- 1) H)) 0)
      )
      (h9 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h9 A B C D E F G H)
        true
      )
      (h10 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h10 A B C D E F G H)
        true
      )
      (h11 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h8 A B C D E F G H)
        true
      )
      (h12 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h12 A B C D E F G H)
        (= (mod H 2) 0)
      )
      (h13 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (h13 A B C D E F I H)
        (= I (+ (- 1) G))
      )
      (h14 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h12 A B C D E F G H)
        (not (= (mod H 2) 0))
      )
      (h15 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h12 A B C D E F G H)
        (not (= (mod H 2) 0))
      )
      (h16 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h11 A B C D E F G H)
        true
      )
      (h17 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h17 A B C D E F G H)
        (= (mod H 2) 0)
      )
      (h18 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h18 A B C D E F G H)
        true
      )
      (h19 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h19 A B C D E F G H)
        (<= (+ F (* (- 2) G)) (- 1))
      )
      (h23 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h19 A B C D E F G H)
        (>= (+ F (* (- 2) G)) 1)
      )
      (h24 A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h23 A B C D E F G H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (h24 A B C D E F G H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
