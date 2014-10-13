Electronic prolate spheroidal orbitals for diatomic molecules
=============================================================

Mathematica notebooks computing electronic prolate spheroidal orbitals for diatomic molecules, i.e., solving the two-center single-electron Schrodinger equation, and calculating Coulomb and exchange integrals of these orbitals; see Ref. 1 and 2 for details. To run the notebooks, the FermiFab toolbox (Ref. 3) is required.

File structure
--------------
* `diatomic_base.m`: Mathematica package defining the core computational routines
* `homonuclear_levels.nb`: single-electron energy levels in dependence of Z*R, homonuclear case, where R is the nuclear distance (bond length) and Z the nuclear charge
* `heteronuclear_levels.nb`: single-electron energy levels, heteronuclear case
* `diatomic_coulomb_m*.nb` pre-computation of Coulomb integral tables
* `oxygen*.nb` ground state energy of the O2 molecule for various symmetries, using the prolate spheroidal orbitals as single-electron basis
* `carbon_monoxide.nb` ground state energy of the CO molecule


License
-------
Copyright (c) 2011-2012, Christian B. Mendl  
All rights reserved.  
http://christian.mendl.net

This program is free software; you can redistribute it and/or
modify it under the terms of the Simplified BSD License
http://www.opensource.org/licenses/bsd-license.php


References
----------
1. Christian B. Mendl  
   Efficient algorithm for two-center Coulomb and exchange integrals of electronic prolate spheroidal orbitals  
   J. Comput. Phys. 231, 5157–5175 (2012), [arXiv:1203.6256](http://arxiv.org/abs/1203.6256)
2. M. Aubert, N. Bessis and G. Bessis  
   Prolate-spheroidal orbitals for homonuclear and heteronuclear diatomic molecules. I. Basic procedure  
   Phys. Rev. A 10, 51–60 (1974) [DOI](http://dx.doi.org/10.1103/PhysRevA.10.51)
3. Christian B. Mendl  
   The FermiFab toolbox for fermionic many-particle quantum systems  
   Comput. Phys. Commun. 182, 1327-1337 (2011), [arXiv:1103.0872](http://arxiv.org/abs/1103.0872)  
   URL http://sourceforge.net/projects/fermifab
