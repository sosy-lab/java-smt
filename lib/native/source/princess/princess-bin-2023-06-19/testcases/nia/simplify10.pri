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
	5*a*a = 2*a
 ->
        a*(a-2*a*(a+3*a*(a-4*a*(a+5*a*(a-6*a*(a+7*a*(a-8*a*(9+a)))))))) = 0
 ->
        a * a * a * a * a * a * a * a * 2
        = a * 612 + a * a * -1 + a * a * a * -2 + a * a * a * a * a * 2 + a * a * a * a * a * a * -2 + a * a * a * a * a * a * a * -2
}


