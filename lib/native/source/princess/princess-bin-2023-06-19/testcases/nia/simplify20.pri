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
	int x1;
	int x2;
	int x3;
	int x4;
	int x5;
}

\problem {
	-5*x1 -2*x2 + x3 -x4 + x5 = 0
->
	9*x1 + 62*x2 -5*x3 -3*x4 + 101*x5 = 0
->
	56*x1 -34*x2 -11*x3 +67*x4 -98*x5 = 0
->
	\exists int k; x5 = 2*k
}


