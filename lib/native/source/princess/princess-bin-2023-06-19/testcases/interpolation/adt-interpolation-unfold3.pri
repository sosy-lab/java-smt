\sorts {
  Union {
    U2(Union2 union2);
  };
  Union2 {
    nil;
    Col1(Col c1);
  };
  Col {
    red; blue;
  };
}

\functions {
  Union u1, u2, u3;
}

\problem {
   \part[p1] (\size(u1) = 3 & u1 != u2)
&  \part[p2] (\size(u2) = 3 & u2 != u3)
&  \part[p3] (\size(u3) = 3 & u1 != u3)

-> false
}

\interpolant{p1, p2; p3}
\interpolant{p2; p1, p3}

