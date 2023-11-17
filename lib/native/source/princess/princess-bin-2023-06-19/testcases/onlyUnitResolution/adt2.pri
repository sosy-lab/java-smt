\sorts {
  Colour { red; green; blue; };
  Pair { Pair(int x, Colour c); };
}

\functions {
  Pair inc(Pair p) { Pair(p.x + 1, p.c) };
  Pair p;
  int f(Pair);
}

\problem {
  \forall Pair p; f(p) = \abs(p.x)
->
  f(p) != f(inc(p))
}
