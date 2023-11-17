/**
 In many cases, neither totality nor functionality axioms are
 necessary to make Princess do interesting things, which can
 lead to significant speedups.

 Totality axioms can often be left out if it is evident from the
 problem formulation that the function is defined in the relevant
 places.

 Functionality can often be left out if a function is uniquely defined
 by axioms (which implies functionality).
 */

\existentialConstants {
  int a, b;
}

\functions {
  \relational \partial int succ(int);
}

\problem {
  \forall int x, y1, y2; {succ(x)} (succ(x) = x+1)
->
  succ(a) = 17 & succ(a) = succ(succ(b))
}