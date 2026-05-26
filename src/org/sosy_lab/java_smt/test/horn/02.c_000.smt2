(set-logic HORN)


(declare-fun |h10| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h21| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h22| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h15| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h23| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h20| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h8| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h16| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h4| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h11| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h13| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |h3| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h17| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h6| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h14| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h12| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h5| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h7| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h19| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h18| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h9| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |h2| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int) (v_13 Int) (v_14 Int) (v_15 Int) )
    (=>
      (and
        (and true
     (= v_8 A)
     (= v_9 B)
     (= v_10 C)
     (= v_11 D)
     (= v_12 E)
     (= v_13 F)
     (= v_14 G)
     (= v_15 H))
      )
      (h1 A B C D E F G H v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) )
    (=>
      (and
        (h1 A B C D E F G H Q R S T U V O P)
        (and (= M 0) (= L 0) (= K 1) (= J 0) (= I 1) (= N 0))
      )
      (h2 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h2 A B C D E F G H I J K L M N O P)
        true
      )
      (h3 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h3 A B C D E F G H I J K L M N O P)
        true
      )
      (h4 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h4 A B C D E F G H I J K L M N O P)
        true
      )
      (h5 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h19 A B C D E F G H I J K L M N O P)
        true
      )
      (h5 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h5 A B C D E F G H I J K L M N O P)
        true
      )
      (h6 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h6 A B C D E F G H I J K L M N O P)
        true
      )
      (h7 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h7 A B C D E F G H I J K L M N O P)
        true
      )
      (h8 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h8 A B C D E F G H I J K L M N O P)
        (<= O (- 1))
      )
      (h9 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) )
    (=>
      (and
        (h9 A B C D E F G H I J Q L R N O P)
        (and (= Q (+ 1 (* (- 1) L) (* (- 1) N) K (* (- 1) M))) (= R (+ (- 1) M)))
      )
      (h10 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) )
    (=>
      (and
        (h11 A B C D E F G H I J Q L R N O P)
        (and (= Q (+ 1 (* (- 1) L) (* (- 1) N) K (* (- 1) M))) (= R (+ (- 1) M)))
      )
      (h10 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h8 A B C D E F G H I J K L M N O P)
        (>= O 1)
      )
      (h11 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h8 A B C D E F G H I J K L M N O P)
        (= O 0)
      )
      (h12 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h12 A B C D E F G H I J K L M N O P)
        true
      )
      (h13 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h13 A B C D E F G H I J K L M N O P)
        true
      )
      (h14 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h10 A B C D E F G H I J K L M N O P)
        true
      )
      (h15 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h15 A B C D E F G H I J K L M N O P)
        true
      )
      (h16 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (h16 A B C D E F G H I J K Q M N O P)
        (= Q (+ (- 1) L))
      )
      (h17 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h15 A B C D E F G H I J K L M N O P)
        true
      )
      (h18 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (h18 A B C D E F G H I J K L M Q O P)
        (= Q (+ (- 2) N))
      )
      (h19 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (h20 A B C D E F G H I J K L M Q O P)
        (= Q (+ (- 2) N))
      )
      (h19 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (h17 A B C D E F G H I J K L M Q O P)
        (= Q (+ (- 2) N))
      )
      (h19 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h15 A B C D E F G H I J K L M N O P)
        true
      )
      (h20 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h14 A B C D E F G H I J K L M N O P)
        true
      )
      (h21 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h21 A B C D E F G H I J K L M N O P)
        (<= (+ L (* (- 1) M)) (- 1))
      )
      (h22 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h21 A B C D E F G H I J K L M N O P)
        (>= (+ L (* (- 1) M)) 1)
      )
      (h23 A B C D E F G H I J K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h22 A B C D E F G H I J K L M N O P)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) )
    (=>
      (and
        (h23 A B C D E F G H I J K L M N O P)
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
