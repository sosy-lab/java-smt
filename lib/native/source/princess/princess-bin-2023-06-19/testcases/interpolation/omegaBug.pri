\predicates {
  inArray(int);
  inSigned(int, int);
  inUnsigned(int, int);
}

\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);
}

\problem {
        \forall int ar, ind, val;
             {select(store(ar, ind, val), ind)}
             select(store(ar, ind, val), ind) = val
->
        \forall int ar, ind1, ind2, val;
             {select(store(ar, ind1, val), ind2)}
             (ind1 != ind2 ->
              select(store(ar, ind1, val), ind2) = select(ar, ind2))
->

\part[p0000] (true) &
\part[p0001] (((sym0<=268435456) & (sym1=sym2) & (sym0>=1))) &
\part[p0002] (true) &
\part[p0003] (((sym3=1) & (sym4=2) & (sym5=sym3))) &
\part[p0004] ((sym3<20)) &
\part[p0005] ((sym6=store(sym1,sym3,12))) &
\part[p0006] ((sym4<20)) &
\part[p0007] (((sym7=store(sym6,sym4,3)) & (sym8=sym9))) &
\part[p0008] ((sym8=0)) &
\part[p0009] (true) &
\part[p0010] ((sym5<20)) &
\part[p0011] ((select(sym7,sym5)=12)) &
\part[p0012] (true) &
\part[p0013] (true) &
\part[p0001] inSigned(32, sym0) & 
\part[p0001] inArray(sym1) & 
\part[p0001] \forall int i; {select(sym2,i)} ((0 <= i & i < 20) -> select(sym2,i)=0) & 
\part[p0003] inUnsigned(32, sym3) & 
\part[p0003] inUnsigned(32, sym4) & 
\part[p0003] inUnsigned(32, sym5) & 
\part[p0005] inArray(sym6) & 
\part[p0007] inArray(sym7) & 
\part[p0007] inUnsigned(32, sym8) & 
\part[p0007] inUnsigned(32, sym9)
-> false
}
\functions {
int sym0, sym1, sym2, sym3, sym4, sym5, sym6, sym7, sym8, sym9;
}
