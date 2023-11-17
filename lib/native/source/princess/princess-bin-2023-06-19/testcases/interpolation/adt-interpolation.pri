\sorts {
  List { nil; cons(int head, List tail); };
}

\functions {
  List l;
}

\problem {
  \part[left] l.is_cons -> \part[right] l = cons(l.head, l.tail)
}

\interpolant {left; right}