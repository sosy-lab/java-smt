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
//                 Eye  Ear  Leg  Arm
  \partial int inj(int, int, int, int);
}

\problem {
  inj(0,0,0,0) + inj(0,0,0,1) + inj(0,0,1,0) + inj(0,0,1,1) +
  inj(0,1,0,0) + inj(0,1,0,1) + inj(0,1,1,0) + inj(0,1,1,1) +
  inj(1,0,0,0) + inj(1,0,0,1) + inj(1,0,1,0) + inj(1,0,1,1) +
  inj(1,1,0,0) + inj(1,1,0,1) + inj(1,1,1,0) + inj(1,1,1,1) = 100
&
  inj(1,0,0,0) + inj(1,0,0,1) + inj(1,0,1,0) + inj(1,0,1,1) +
  inj(1,1,0,0) + inj(1,1,0,1) + inj(1,1,1,0) + inj(1,1,1,1) = 70
&
  inj(0,1,0,0) + inj(0,1,0,1) + inj(0,1,1,0) + inj(0,1,1,1) +
  inj(1,1,0,0) + inj(1,1,0,1) + inj(1,1,1,0) + inj(1,1,1,1) = 75
&
  inj(0,0,1,0) + inj(0,0,1,1) +
  inj(0,1,1,0) + inj(0,1,1,1) +
  inj(1,0,1,0) + inj(1,0,1,1) +
  inj(1,1,1,0) + inj(1,1,1,1) = 85
&  
  inj(0,0,0,1) + inj(0,0,1,1) +
  inj(0,1,0,1) + inj(0,1,1,1) +
  inj(1,0,0,1) + inj(1,0,1,1) +
  inj(1,1,0,1) + inj(1,1,1,1) = 80
&
  \forall int x1, x2, x3, x4; {inj(x1, x2, x3, x4)} inj(x1, x2, x3, x4) >= 0
->
  inj(1, 1, 1, 1) >= MinNum
}
