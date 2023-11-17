\problem {
  \forall int a, b; (a = b -> eqArrays(a, b) = 0)
&
  \forall int a, b, x; (eqArrays(a, b)=0 -> select(a, x) = select(b, x))
&
  \forall int a; (eqArrays(a, a)=0)
&
  \forall int a, b, c; (eqArrays(a, b)=0 -> eqArrays(b, c)=0 -> eqArrays(a, c)=0)
&
  \forall int a, b; (eqArrays(a, b)=0 -> eqArrays(b, a)=0)
&
  \forall int a, b, x, i; (eqArrays(a, b)=0 -> eqArrays(store(a, x, i), store(b, x, i))=0)
&
  \forall int a, b, x, i, j;
     (eqArrays(store(a, x, i), store(b, x, j))=0 -> i = j)
}
