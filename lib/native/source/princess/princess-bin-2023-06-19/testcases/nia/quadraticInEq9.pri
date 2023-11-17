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
	int a; int b; int c; int d; int e;  int f; int g; int h; int i;
}

\problem {
	e < a & a <= d & i < h & h < g & g <= f
	&
	a * f - a * h <= b + c * g - c * h
->
	e * f - e * i <= b + c * g - c * h + d * h - d * i
}


