/**
 Find a linear ranking function for the program

 
 while (x >= 0) {
   x = x + 1
 }

 where x ranges over [-8, 7], i.e., 4-bit arithmetic is used.

 (none exists)
 */

\existentialConstants {
  int lambda11_1;
  int lambda11_2;
  int lambda11_3;
  int lambda11_4;
  int lambda11_5;
  int lambda11_6;

  int lambda12_1;
  int lambda12_2;
  int lambda12_3;
  int lambda12_4;
  int lambda12_5;
  int lambda12_6;

  int lambda21_1;
  int lambda21_2;
  int lambda21_3;
  int lambda21_4;
  int lambda21_5;
  int lambda21_6;

  int lambda22_1;
  int lambda22_2;
  int lambda22_3;
  int lambda22_4;
  int lambda22_5;
  int lambda22_6;

  int rankingCoeff1;
  int rankingCoeff2;
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
&

//   lambdas non-negative

  lambda11_1 >= 0 &
  lambda11_2 >= 0 &
  lambda11_3 >= 0 &
  lambda11_4 >= 0 &
  lambda11_5 >= 0 &
  lambda11_6 >= 0 &
  lambda12_1 >= 0 &
  lambda12_2 >= 0 &
  lambda12_3 >= 0 &
  lambda12_4 >= 0 &
  lambda12_5 >= 0 &
  lambda12_6 >= 0 &
  lambda21_1 >= 0 &
  lambda21_2 >= 0 &
  lambda21_3 >= 0 &
  lambda21_4 >= 0 &
  lambda21_5 >= 0 &
  lambda21_6 >= 0 &
  lambda22_1 >= 0 &
  lambda22_2 >= 0 &
  lambda22_3 >= 0 &
  lambda22_4 >= 0 &
  lambda22_5 >= 0 &
  lambda22_6 >= 0
}