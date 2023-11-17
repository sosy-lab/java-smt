
\predicates {
  abBounded { max(a, b) <= lim };
}

\functions {
  int a, b;
  int max(int x, int y) { \if (x > y) \then (x) \else (y) };
}

\functions {
  int inInterval(int x) { limited(\max(x, 0)) };
  int limited(int x) { \if (x > lim) \then (lim) \else (x) };
}

\functions {
  int lim;
}

\problem {
  (max(a, b) = \max(a, b))
&
  limited(a) <= lim
&
  limited(lim) = lim
&
  inInterval(a) <= lim
&
  (abBounded -> (a + b) / 2 <= lim)
}