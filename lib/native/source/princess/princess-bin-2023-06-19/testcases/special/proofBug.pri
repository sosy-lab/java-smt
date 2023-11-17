// This example was previously provable (or alternatively led
// to an assertion failure)

\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int complement(int);
  \partial int size(int);

  int A, B, C;
  int empty;
}

\problem {
  \forall int x, y; {intersect(x, y)} intersect(x, y) = intersect(y, x)
->

  \forall int x; {complement(complement(x))} complement(complement(x)) = x
->
  \forall int x; {intersect(x, complement(x))} intersect(x, complement(x)) = empty
->
  size(empty) = 0
->

  \forall int x, y; {size(intersect(x, y))}
     size(x) = size(intersect(x, y)) + size(intersect(x, complement(y)))

->
  \forall int x; {size(x)} size(x) >= 0
->
  
  \part[left]  !(size(intersect(A, complement(B))) = 0)
//&
//  \part[right]  size(intersect(union(A, C), complement(B))) = 0

->
  false
}

\interpolant{left; right}
