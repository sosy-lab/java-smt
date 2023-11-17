\problem {
  \forall int a;
  (\eps int div; (2*div <= a & 2*div >= a - 1)) * 2 +                 // div
  (\eps int modulus; (modulus >= 0 & modulus < 2 & \exists int x; a - modulus = 2*x)) // mod
  = a
}