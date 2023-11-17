
\functions {
   signed bv[8] x, a, b;
   signed bv[8] c;
}

\problem {

  \part[cond]          (a = 2*x & a >= 0 & a < 50) &
  \part[stmt1]    b = a/2 & 
  \part[stmt2]         c=(3*b+1)
                       ->
  \part[assert]        c > a
}

/* Interpolation specification */
\interpolant {cond; stmt1; stmt2; assert}
