/**
 * Inductive proof showing that
 * lexComp(l1, l2) & lexComp(l2, l1) <-> l1 = l2
 */

\sorts {
  /* Declare sorts and algebraic data-types */
  List { nil; cons(int head, List tail); };
}

\functions {
  List l1, l2;
  bool lexComp(List, List);
}

\predicates {
  For(List l1, List l2) {
    lexComp(l1, l2) & lexComp(l2, l1) <-> l1 = l2
  };
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
->

  \forall List l1', l2'; (\size(l1') < \size(l1) -> For(l1', l2'))
->
  For(l1, l2)

}
