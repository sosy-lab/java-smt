/*
   Solve with options "-generateTriggers=all +mostGeneralConstraint"
 */

\existentialConstants {
  int MinNum;
}

\functions {
  \partial int inj(int);
  \partial int sum(int);
  \partial int pSum(int, int);
  \partial int bit(int, int);
}

\problem {
// Recursive extraction of individual bits in an integer number
  \forall int x1, x2, b; {bit(2*x1 + x2, b)} (
     x2 >= 0 & x2 < 2 ->
        (b > 0 -> bit(2*x1 + x2, b) = bit(x1, b-1)) &
        (b = 0 -> bit(2*x1 + x2, b) = x2)
  )

// Recursive computation of the sum "inj(0) + inj(1) + ... + inj(15)"
&
  sum(0) = 0
&
  \forall int x; {sum(x)} (x>0 -> sum(x) = sum(x-1) + inj(x-1))

// Recursive computation of the sum of the inj(i), for those i where bit b is set
&
  \forall int b; pSum(0, b) = 0
&
  \forall int x, b; {pSum(x, b)} (
     x>0 -> pSum(x, b) = pSum(x-1, b) + (\if (bit(x-1, b) = 1) \then (inj(x-1)) \else (0)))

& sum(16) = 100        // 100 soldiers altogether
& pSum(16, 0) = 70     // 70 soldiers lost an eye
& pSum(16, 1) = 75     // 75 soldiers lost an ear
& pSum(16, 2) = 85     // 85 soldiers lost a leg
& pSum(16, 3) = 80     // 80 soldiers lost an arm

&
// inj is non-negative
  \forall int x; inj(x) >= 0

->
// MinNum is supposed to be a lower bound of the number of soldiers who must have lost all 4
  inj(15) >= MinNum
}

