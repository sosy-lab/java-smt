\predicates {
  p(int);
}

\functions {
  int x;
}

\problem {
  \part[left] (x >= 0 & x <= 3 & p(x))
->
  \part[middle] p(0) | \part[right] (p(1) | p(2)) | \part[middle] p(3)
}

\interpolant { left; middle; right }

