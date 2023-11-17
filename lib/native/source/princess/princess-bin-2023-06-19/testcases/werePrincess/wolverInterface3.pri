/**
 * Array example taken from "An interpolating theorem prover"
 */

\functions {
  int M, M', a, x, b, c;
}
\problem {
  \part[p0] M' = store(M, a, x) &
  \part[p1] (b != c & select(M',b) != select(M,b) & select(M',c) != select(M,c))
  ->
  false 
}
