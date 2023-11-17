\functions {
  int a, b;
}
\predicates {
  p;
}
\problem {
  \exists int y;
    2*y = \if (\exists int x;
                 a = \if (p) \then (2*x) \else ((1+1)*x))
          \then (a) \else (a+1)
}