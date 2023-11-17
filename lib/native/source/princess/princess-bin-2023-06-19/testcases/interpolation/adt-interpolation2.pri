\sorts {
  Colour { red; green; blue; };
  List{ nil; cons(Colour head, List tail); };
}

\functions {
  List l, l2;
}

\problem {
  \part[left] l = cons(red, l2)
->
  \part[right] l.is_nil

-> false
  
}

\interpolant{left; right}