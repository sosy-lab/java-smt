
\existentialConstants {
  int A;
}
        
\universalConstants {
  int B;
}
        
\predicates {
  gcd(int, int, int);
}
        
\problem {
  /* Problem to be proven */
      
             \forall int y; gcd(0, y, y)
          -> \forall int x, y, z; (gcd(x, y, z) <-> gcd(x, y+x, z))
          -> \forall int x, y, z; (gcd(x, y, z) <-> gcd(y, x, z))
          ->
             gcd(0,B,A)
}
