// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


\functions {
	int a; int b; int c;
}

\problem {
	(a+b+c+1) *
	(a+b+c+1) *
	(a+b+c+1) *
	(a+b+c+1) = 0
->
  c * c * c * c
 =   -1
   + a * -4
   + a * a * -6
   + a * a * a * -4
   + a * a * a * a * -1
   + b * -4
   + b * a * -12
   + b * b * -6
   + b * a * a * -12
   + b * b * a * -12
   + b * b * b * -4
   + b * a * a * a * -4
   + b * b * a * a * -6
   + b * b * b * a * -4
   + b * b * b * b * -1
   + c * -4
   + c * a * -12
   + c * b * -12
   + c * c * -6
   + c * a * a * -12
   + c * b * a * -24
   + c * b * b * -12
   + c * c * a * -12
   + c * c * b * -12
   + c * c * c * -4
   + c * a * a * a * -4
   + c * b * a * a * -12
   + c * b * b * a * -12
   + c * b * b * b * -4
   + c * c * a * a * -6
   + c * c * b * a * -12
   + c * c * b * b * -6
   + c * c * c * a * -4
   + c * c * c * b * -4
}


