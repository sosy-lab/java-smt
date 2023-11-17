\sorts {
  Union {
    nil;
    Col1(Col c1);
    Col2(Col c2, Col c3);
  };
  Col {
    red; blue; green;
  };
}

\functions {
  Union u1, u2;
}

\problem {
   \part[left] \size(u1) = 1
&  \part[right] (u1 != u2 & \size(u2) = 1)

-> false
}

\interpolant{left; right}
\interpolant{right; left}
