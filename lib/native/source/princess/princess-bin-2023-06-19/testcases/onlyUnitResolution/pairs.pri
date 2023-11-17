\sorts {
  Pair { Pair(bool left, bool right); };
}

\universalConstants {
  /* Declare universally quantified constants of the problem */
  
}

\existentialConstants {
  /* Declare existentially quantified constants of the problem */
  
}

\functions {
  /* Declare constants and functions occurring in the problem
   * (implicitly universally quantified).
   * The keyword "\partial" can be used to define functions without totality axiom,
   * while "\relational" can be used to define "functions" without functionality axiom. */
  Pair p, q; nat x;
}

\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified) */  
  
}

\problem {
  p.left != p.right
&
  p != q

->
  false
}
