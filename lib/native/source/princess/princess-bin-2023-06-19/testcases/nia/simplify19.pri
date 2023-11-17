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
	int x0;
	int x1;
	int x2;
	int x3;
	int x4;
	int x5;
	int x6;
	int x7;
	int x8;
	int x9;
}

\problem {
	x0 = 5*x1+1
->
	4*x1 = 5*x2+1
->
	4*x2 = 5*x3+1
->
	4*x3 = 5*x4+1
->
	4*x4 = 5*x5+1
->
	4*x5 = 5*x6+1
->
	4*x6 = 5*x7+1
->
	4*x7 = 5*x8+1
->
	4*x8 = 5*x9+1
->
	\exists int k; (x0 + 4) = 1953125*k
}


