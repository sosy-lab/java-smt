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
	(a != 0 -> 0 / a = 0)
&
	(a != 0 -> b / a * a <= b)
// &
//	(d >= 0 & b >= a & a > 0 -> d / b <= d / a)
}


