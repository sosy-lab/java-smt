// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001 Universitaet Karlsruhe, Germany
//                    and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

// File     : SET027+3 : TPTP v2.5.0. Released v2.2.0.
// Domain   : Set Theory (Boolean properties)
// Problem  : Transitivity of subset
// Version  : [Try89] axioms : Reduced > Incomplete.
// English  : If X is a subset of Y and Y is a subset of Z, then X is a 
//            subset of Z.



\predicates {
  member(int, int);
  subset(int, int);
}


\problem {
     \forall int x1;
       \forall int x2;
          \forall int x3;
         (    subset(x1, x2)
          ->
                (member(x3, x1) -> member(x3, x2)))
->
     \forall int x1;
       \forall int x2;
         \exists int x3;
         ((member(x3, x1) -> member(x3, x2))
          -> subset(x1, x2) )
-> \forall int x4;  subset(x4, x4)
-> \forall int x5; 
     \forall int x6; 
       \forall int x7; 
         (   subset(x5, x6) & subset(x6, x7)
          -> subset(x5, x7))

}

