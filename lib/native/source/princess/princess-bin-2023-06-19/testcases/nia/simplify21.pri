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
	int x6;
	int x;
}

\problem {
	x = 1000
->
	1*x6 + x*x5 + x*x4 + x*x3 + x*x2 + x*x1 = 0
->
	x*x6 + (-1)*x5 + (-1)*x4 + (-1)*x3 + (-1)*x2 + (-1)*x1 = 0
->
	x*x6 + 1*x5 + (-1)*x4 + (-1)*x3 + (-1)*x2 + (-1)*x1 = 0
->
	x*x6 + 0*x5 + (1)*x4 + (1)*x3 + (1)*x2 + (1)*x1 = 0
->
	x*x6 + 0*x5 + (-1)*x4 + (1)*x3 + (1)*x2 + (1)*x1 = 0
->
	x*x6 + 0*x5 + 0*x4 + (-1)*x3 + (-1)*x2 + (-1)*x1 = 0
->
	x*x6 + 0*x5 + 0*x4 + (1)*x3 + (-1)*x2 + (-1)*x1 = 0
->
	x*x6 + 0*x5 + 0*x4 + 0*x3 + (1)*x2 + (1)*x1 = 0
->
	x*x6 + 0*x5 + 0*x4 + 0*x3 + (-1)*x2 + (1)*x1 = 0
->
	x*x6 + 0*x5 + 0*x4 + 0*x3 + 0*x2 + (-1)*x1 = 0
->
	x1=0 & x2=0 & x3=0 & x4=0 & x5=0 & x6=0
}


