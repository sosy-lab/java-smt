/*

Riddle taken from http://brainden.com/forum/index.php/topic/14-cost-of-war/

Here's a variation on a famous puzzle by Lewis Carroll, who wrote Alice's Adventures in Wonderland.
A group of 100 soldiers suffered the following injuries in a battle: 70 soldiers lost an eye, 75 lost an ear, 85 lost a leg, and 80 lost an arm.
What is the minimum number of soldiers who must have lost all 4?

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
  sum(0) = 0
&
  \forall int x; {sum(x)} (x>0 -> sum(x) = sum(x-1) + inj(x-1))

&
  \forall int x1, x2, b; {bit(2*x1 + x2, b)} (
     x2 >= 0 & x2 < 2 ->
        (b > 0 -> bit(2*x1 + x2, b) = bit(x1, b-1)) &
        (b = 0 -> bit(2*x1 + x2, b) = x2)
  )

&
  \forall int b; pSum(0, b) = 0
&
  \forall int x, b; {pSum(x, b)} (x>0 -> pSum(x, b) = pSum(x-1, b) +
                      (\if (bit(x-1, b) = 1) \then (inj(x-1)) \else (0)))

&
  sum(16) = 100
&
  pSum(16, 0) = 70
&
  pSum(16, 1) = 75
&
  pSum(16, 2) = 85
&
  pSum(16, 3) = 80

&
  \forall int x; inj(x) >= 0

->
  inj(15) >= MinNum
}
