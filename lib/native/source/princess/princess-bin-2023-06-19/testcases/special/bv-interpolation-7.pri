// Previously this case lead to non-termination
// (but only when generating proofs)

\functions {
  bv[3] x, y, z;  
}

\problem {
  \part[p1] 3*x + 4*y + 2*z = 0 &
  \part[p2] 2*x + 2*y + 2 = 0 &
  \part[p3] 4*y + 2*x + z*z*z = 0

-> false
}

\interpolant{p1; p2; p3}
\interpolant{p1, p3; p2}
