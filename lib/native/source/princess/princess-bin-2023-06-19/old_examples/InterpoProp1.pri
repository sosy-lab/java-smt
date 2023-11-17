\predicates {
p;
}

\functions {
  int x, a, b, c;
}

\problem {
  \part[bla] p &
  \part[cond]          (a-2*x = 0 & -a <= 0) &
  \part[stmt1]         (2*b - a <=0 & -2*b + a -1 <=0) &
  \part[stmt2]         (p <-> c-3*b-1=0)
                       ->
  \part[assert]        c > a
}

\interpolant {cond, stmt2; bla, stmt1, assert}
