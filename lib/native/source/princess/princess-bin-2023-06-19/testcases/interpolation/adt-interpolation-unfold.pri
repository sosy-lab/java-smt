\sorts {
  Nat {
    one; succ(Nat pred);
  };
}

\functions {
  Nat x, y;
}

\problem {
  \part[p1] \size(x) = 3 &
  \part[p2] \size(y) = 3 &
  \part[p3] x != y

-> false
}

\interpolant{p1, p3; p2}
\interpolant{p1; p3, p2}
\interpolant{p1, p2; p3}
