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
	int a; int b; int c; int d; int e;
}

\problem {
        a*a + (a+b)*(c+d+1)*(a+2) + b = (a+b+c+d)*(2+c)
        ->
   d * b * a
 =   a * a * -2
   - c * a
   - b
   - b * a
   + c * 2
   - c * b
   + c * c
   - c * a * a
   - d * a * 2
   - d * b * 2
   - c * b * a
   + d * c
   - d * a * a
   + d * 2
}


