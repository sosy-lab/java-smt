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
	\part[A] 0 < a * b &
        \part[B] 0 < c * d &
        \part[C] 0 < a * c
->
	\part[D] 0 < b * d
}

\interpolant { A; B; C; D }

