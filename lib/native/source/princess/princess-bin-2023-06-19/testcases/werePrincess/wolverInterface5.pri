\problem {
\part[p0000] (true) &
\part[p0001] (((sym0<=268435456) & (sym0>=1))) &
\part[p0002] (true) &
\part[p0003] (((sym1<5) & (sym2=sym1))) &
\part[p0004] ((sym2!=0)) &
\part[p0005] ((sym3=and(addUnsigned(2*1024*1024*1024, 4294967295, sym2), sym2))) &
\part[p0006] (!((sym1>=sym3))) &
\part[p0001] inSigned(2*1024*1024*1024, sym0) & 
\part[p0003] inUnsigned(2*1024*1024*1024, sym1) & 
\part[p0003] inUnsigned(2*1024*1024*1024, sym2) & 
\part[p0005] inUnsigned(2*1024*1024*1024, sym3)
-> false
}
\functions {
int sym0, sym1, sym2, sym3;
}
