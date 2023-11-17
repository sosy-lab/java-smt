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
	a*a + 10 >= 0
	&
	a*a*a*a + a*a + 10 >= 0
	&
	(a*a >= 4 -> (a >= 2 | a <= -2))
	&
	(a*a = 1 <-> (a = 1 | a = -1))
	&
	(a*b = 1 <-> (a = b & (a = 1 | a = -1)))
	&
	(a*a = 2 -> false)
	&
	(a*a >= a)
	&
	(a * b * b * c = 0 <-> (a = 0 | b = 0 | c = 0))
}
