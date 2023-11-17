// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001 Universitaet Karlsruhe, Germany
//                    and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

// File     : SET043+1 : TPTP v2.5.0. Released v2.0.0.
// Domain   : Set Theory
// Problem  : Russell's Paradox
// Version  : Especial.
// English  : Russell's paradox : there is no Russell set (a set which 
//            contains exactly those sets which are not members 
//            of themselves).



\predicates {
  member(int, int);
  subset(int, int);
}


\problem {
!\exists int x1;
   \forall int x2; (member(x2, x1) <-> !member(x2, x2))

}

