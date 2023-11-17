// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001 Universitaet Karlsruhe, Germany
//                    and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

// File     : SET063+3 : TPTP v2.5.0. Released v2.2.0.
// Domain   : Set Theory (Boolean properties)
// Problem  : If X is a subset of the empty set, then X is the empty set
// Version  : [Try89] axioms : Reduced > Incomplete.
// English  : 


\functions {
  int empty_set;
}

\predicates {
  empty(int);
  member(int, int);
  subset(int, int);
  equal(int, int);
}


\problem {
     \forall int x1;  subset(empty_set, x1)
   & \forall int x2;  !member(x2, empty_set)
   & \forall int x3; 
       \forall int x4; 
         (    subset(x3, x4)
          <-> \forall int x5; 
                (member(x5, x3) -> member(x5, x4)))
   & \forall int x6; 
       \forall int x7; 
         (    equal(x6, x7)
          <-> subset(x6, x7) & subset(x7, x6))
   & \forall int x8;  subset(x8, x8)
   & \forall int x9; 
       (empty(x9) <-> \forall int x0;  !member(x0, x9))
-> \forall int y1; 
     (subset(y1, empty_set) -> equal(y1, empty_set))

}

