/**
 Find a linear ranking function for the program

 
 while (x >= 0) {
   x = x + 1
 }

 where x ranges over [-8, 7], i.e., 4-bit arithmetic is used.

 (none exists)
 */

\existentialConstants {
  nat lambda11_1;
  nat lambda11_2;
  nat lambda11_3;
  nat lambda11_4;
  nat lambda11_5;
  nat lambda11_6;

  nat lambda12_1;
  nat lambda12_2;
  nat lambda12_3;
  nat lambda12_4;
  nat lambda12_5;
  nat lambda12_6;

  nat lambda21_1;
  nat lambda21_2;
  nat lambda21_3;
  nat lambda21_4;
  nat lambda21_5;
  nat lambda21_6;

  nat lambda22_1;
  nat lambda22_2;
  nat lambda22_3;
  nat lambda22_4;
  nat lambda22_5;
  nat lambda22_6;

  nat rankingCoeff1;
  nat rankingCoeff2;
}

\problem {
  
//   lambdai1 Ai' = 0

  lambda11_1 * 0 + lambda11_2 * 0 + lambda11_3 * -1 + lambda11_4 * 1 + lambda11_5 * 1 + lambda11_6 * -1 = 0
&
  lambda21_1 * 0 + lambda21_2 * 0 + lambda21_3 * -1 + lambda21_4 * 1 + lambda21_5 * 1 + lambda21_6 * -1 = 0
&

//   (lambdai1 - lambdai2) Ai = 0

  (lambda11_1 - lambda12_1) * -1 + (lambda11_2 - lambda12_2) * 1 + (lambda11_3 - lambda12_3) * 0 +
  (lambda11_4 - lambda12_4) * 0 + (lambda11_5 - lambda12_5) * -1 + (lambda11_6 - lambda12_6) * 1 = 0
&  
  (lambda21_1 - lambda22_1) * -1 + (lambda21_2 - lambda22_2) * 1 + (lambda21_3 - lambda22_3) * 0 +
  (lambda21_4 - lambda22_4) * 0 + (lambda21_5 - lambda22_5) * -1 + (lambda21_6 - lambda22_6) * 1 = 0
&  

//   lambdai2 (Ai + Ai') = 0

  lambda12_1 * (-1 + 0) + lambda12_2 * (1 + 0) + lambda12_3 * (0 + -1) + lambda12_4 * (0 + 1) + lambda12_5 * (-1 + 1) + lambda12_6 * (1 + -1) = 0
&
  lambda22_1 * (-1 + 0) + lambda22_2 * (1 + 0) + lambda22_3 * (0 + -1) + lambda22_4 * (0 + 1) + lambda22_5 * (-1 + 1) + lambda22_6 * (1 + -1) = 0  
&

//   lambdai2 bi < 0

  lambda12_1 * 8 + lambda12_2 * 7 + lambda12_3 * 8 + lambda12_4 * 7 + lambda12_5 * 1 + lambda12_6 * -1 < 0
&
  lambda22_1 * 8 + lambda22_2 * 7 + lambda22_3 * 8 + lambda22_4 * 7 + lambda22_5 * -15 + lambda22_6 * 15 < 0
&

//   lambda12 A1' = lambda22 A2'

  rankingCoeff1 = lambda12_1 * 0 + lambda12_2 * 0 + lambda12_3 * -1 + lambda12_4 * 1 + lambda12_5 * 1 + lambda12_6 * -1
&
  rankingCoeff2 = lambda22_1 * 0 + lambda22_2 * 0 + lambda22_3 * -1 + lambda22_4 * 1 + lambda22_5 * 1 + lambda22_6 * -1
&
  rankingCoeff1 = rankingCoeff2
}