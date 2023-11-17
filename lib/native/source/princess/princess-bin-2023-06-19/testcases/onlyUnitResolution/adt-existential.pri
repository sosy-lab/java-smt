\sorts {
  List { nil; cons(int head, List tail); };
}

\existentialConstants {
  List l, m;
}

\problem {
  l.is_cons & l.tail = m & l.head > 0
}

