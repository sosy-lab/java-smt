
\functions {
   signed bv[8] x, a, b;
   signed bv[12] c;
}

\problem {


  \part[cond]          (a = 2*x & a >= 0) &
  \part[stmt1]    b = a/2 & 
  \part[stmt2]         c=(3*b.\as[signed bv[12]]+1)
                       ->
  \part[assert]        c > a.\as[signed bv[12]]
}

/* Interpolation specification */
\interpolant {cond; stmt1; stmt2; assert}
