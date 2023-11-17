\sorts {
  C { red; green; };
  List { nil; cons(C head, List tail); };
}

\functions {
  List l;
}

\problem {
  l.is_cons & l.tail.is_cons & l.tail.tail.is_cons
->
  false
}
