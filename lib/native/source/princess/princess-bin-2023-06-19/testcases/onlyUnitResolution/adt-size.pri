/**
 * Example:
 * Problem over Algebraic Data-Types
 */

/* Definition of Algebraic Data-Types */
\sorts {
  Colour { red; green; blue; };
  List { nil; cons(Colour head, List tail); };
}

/* Definition of functions and variables of the problem */
\functions {
  List l;
  \partial bool gl(List);
}

/* Find a colour list of size < 10 with all adjacent colours distinct */
\problem {
  \forall List l; {gl(l)} (
    gl(l) <-> (\size(l) > 3 -> l.head != l.tail.head & gl(l.tail)))
&
  gl(l) & \size(l) > 3 & \size(l) < 10

 -> false
}
