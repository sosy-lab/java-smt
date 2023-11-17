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
 a*a + (a+b)*(c-d+1)*(a-2) + b = -(a+b+c+d)*(2+c)
 ->
   d * b * a + c * b
  =   a * a * 2
    + b
    + b * a
    + d * b
    + c * 2
    - c * a
    + c * c
    + c * a * a
    + d
    + d * a * 2
    + d * b
    + c * b * a
    + d * c
    - d * a * a
    + d
}


