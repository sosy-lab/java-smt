\sorts {
  Pair { Pair(nat left, bool right); };
}

\functions {
  Pair p;
  int asInt(Pair q) { \if (q.right) \then (q.left) \else (-q.left) };
}

\problem {
  p.left >= 0
&
  -asInt(p) = asInt(Pair(p.left, !p.right))
&
  p = Pair(p.left, p.right)
}
