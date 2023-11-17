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
	int a; int b; int c; int d;
}

\problem {
	a*a + (a*b*c+b*d*a)*(c*c*a+d*d*b+1) + b = (a+b+c+d)*(2+c)
	->
  d * d * d * b * b * a * 1
 =   a * 2
   - a * a
   + b
   + c * 2
   + d * d * c * b * b * a * -1
   + c * a
   + c * b
   - c * b * a
   + c * c * c * b * a * a * -1
   + d * 2
   + d * c
   + d * b * a * -1
   + c * c
   - d * c * c * b * a * a
}


