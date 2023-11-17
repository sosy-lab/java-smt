\functions {
  int sym0, undef0, sym1, undef1, sym2, sym3, undef2, sym4, sym5, sym6, sym7;
}

\problem {
\part[p2] ((sym4=0)) &
\part[p3] ((sym4<5)) &
\part[p4] \exists int k; (sym5=1 + sym4 + k*4*1024*1024*1024 & sym5 >= 0 & sym5 < 4*1024*1024*1024) &
\part[p5] (true) &
\part[p6] (!((sym5<5))) &
\part[p2] (sym4 >= 0 & sym4 < 4*1024*1024*1024)
->
false
}

\interpolant{p2;p3;p4;p5;p6}
