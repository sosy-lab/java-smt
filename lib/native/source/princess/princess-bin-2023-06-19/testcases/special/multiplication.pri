\functions {
  \partial int mul(int, int);
}

\problem {
  \forall int x, y, z; mul(x+y, z) = mul(x,z) + mul(y,z)
->
  \forall int x; {mul(x,0)} mul(x,0) = 0 
->
  \forall int x; {mul(0,x)} mul(0,x) = 0 
->
  \forall int x; {mul(1,x)} mul(1,x) = x 
->
  \forall int x; {mul(x,1)} mul(x,1) = x
->
  mul(2,2) = 4
}
