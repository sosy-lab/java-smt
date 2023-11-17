\functions {
  int a, b, c, d;
  \partial int mul(int, int);
  \partial int add(int, int);
}

\problem {
//  \forall int x, y, a; {mul(x+y, a), mul(x, a)} mul(x+y, a) = mul(x,a) + mul(y,a)
//->
  \forall int x, y; {add(x,y)} add(x,y) = x+y
->
  \forall int x, y, z; {mul(add(x,y),z)} mul(add(x,y),z) = mul(x,z) + mul(y,z)
->
  \forall int x, y, z; {mul(z, add(x,y))} mul(z, add(x,y)) = mul(z,x) + mul(z,y)
->
  \forall int x; {mul(x,0)} mul(x,0) = 0
->
  \forall int x; {mul(0,x)} mul(0,x) = 0
->
  mul(add(a,b),add(c,d)) = mul(a,c) + mul(b,d) + mul(a,d) + mul(b,c)
}