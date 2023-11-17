\predicates {
  p(int, int);
}

\functions {
  int x;
}

\problem {
  \part[left] x = 13
->
  \part[middle] p(x+1, 26)
->
  \part[right] p(14, 2*x)
}

\interpolant { left; middle, right }
