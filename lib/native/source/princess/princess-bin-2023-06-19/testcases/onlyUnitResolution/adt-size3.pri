\sorts {
  /* Declare sorts and algebraic data-types */
  List { nil; cons(int head, List tail); };
}

\functions {
  List l1, l2;
  \partial bool lexComp(List, List);
}

\problem {
  // lexicographic <=
  \forall List l1, l2; {lexComp(l1, l2)} (
    lexComp(l1, l2) <-> (
      l1 = nil |
      l1.is_cons & l2.is_cons & (l1.head < l2.head |
                                 l1.head = l2.head & lexComp(l1.tail, l2.tail))
    )
  )
  & \size(l1) <= 8 & \size(l2) <= 12
  & lexComp(l1, l2) & lexComp(l2, l1)

  -> l1 = l2
}
