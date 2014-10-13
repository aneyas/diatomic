(* ::Package:: *)

(* Abstract Coulomb integrals *)

RemoveSpinCoord[x_]:=Quotient[x-1,2]+1
SetAttributes[RemoveSpinCoord,Listable]

CoulombSymmetry[a_,b_,c_,d_]:=CoulombSymmetry[c,d,a,b]/;a>c\[Or](a==c\[And]b>d)
CoulombSymmetry[a_,b_,c_,d_]:=CoulombSymmetry[b,a,d,c]/;a>b
CoulombSymmetry[a_,b_,c_,d_]:=Module[{qLz={0,0,0,0,0,1,-1,1,-1,0}},If[qLz[[a]]-qLz[[b]]==-(qLz[[c]]-qLz[[d]]),CoulInt[a,b,c,d],0]]

SpinTraceCoulombPart[p0_,p1_,q0_,q1_]:=If[Mod[p0-q0,2]==0\[And]Mod[p1-q1,2]==0,CoulombSymmetry@@RemoveSpinCoord[{p0,q0,p1,q1}],0]
SpinTraceCoulombBase[p0_,p1_,q0_,q1_]:=SpinTraceCoulombPart[p0,p1,q0,q1]-SpinTraceCoulombPart[p0,p1,q1,q0]

DiatomicSpinTraceCoulomb[\[Rho]_]:=Expand[Total[First[#]SpinTraceCoulombBase@@Flatten[FermiToCoords/@Last[#]]&/@\[Rho]]]


(* Products of Laguerre polynomial expansions *)

(* see also: R. D. Lord. Integrals of Products of Laguerre Polynomials.
	Mathematics of Computation 14, 375-376 (1960) *)

(* Integrate[LaguerreL[i1,m1,x]LaguerreL[i2,m2,x]LaguerreL[i3,m3,x]Exp[-z x],{x,0,\[Infinity]}] *)
LaguerreProdInt[{-1,_,_},_,_]=0;
LaguerreProdInt[{_,-1,_},_,_]=0;
LaguerreProdInt[{_,_,-1},_,_]=0;
LaguerreProdInt[i_List,m_List,z_]:=LaguerreProdInt[i,m,z]=FullSimplify[
	-(1/z-1)(LaguerreProdInt[i-{1,0,0},m,z]+LaguerreProdInt[i-{0,1,0},m,z]+LaguerreProdInt[i-{0,0,1},m,z])
	+(2/z-1)(LaguerreProdInt[i-{0,1,1},m,z]+LaguerreProdInt[i-{1,0,1},m,z]+LaguerreProdInt[i-{1,1,0},m,z])
	-(3/z-1) LaguerreProdInt[i-{1,1,1},m,z]+Times@@Binomial[m-1+i,i]/z]

(* Integrate[x^m1 LaguerreL[i1,m1,x]LaguerreL[i2,m2,x]LaguerreL[i3,m3,x]Exp[-z x],{x,0,\[Infinity]}]
   by using the identity x^m LaguerreL[n,m,x]==(n+m)x^(m-1)LaguerreL[n,m-1,x]-(n+1)x^(m-1)LaguerreL[n+1,m-1,x] *)
LaguerreProdIntX1[i_List,{0,m2_,m3_},z_]:=LaguerreProdInt[i,{0,m2,m3},z]
LaguerreProdIntX1[i_List,m_List,z_]:=LaguerreProdIntX1[i,m,z]=
	FullSimplify[First[i+m]LaguerreProdIntX1[i,m-{1,0,0},z]-(First[i]+1)LaguerreProdIntX1[i+{1,0,0},m-{1,0,0},z]]

(* Integrate[x^(m1+m2) LaguerreL[i1,m1,x]LaguerreL[i2,m2,x]LaguerreL[i3,m3,x]Exp[-z x],{x,0,\[Infinity]}]
   by using the identity x^m LaguerreL[n,m,x]==(n+m)x^(m-1)LaguerreL[n,m-1,x]-(n+1)x^(m-1)LaguerreL[n+1,m-1,x] *)
LaguerreProdIntX12[{i1_,i2_,i3_},{0,m2_,m3_},z_]:=LaguerreProdIntX1[{i2,i1,i3},{m2,0,m3},z]
LaguerreProdIntX12[i_List,m_List,z_]:=LaguerreProdIntX12[i,m,z]=
	FullSimplify[First[i+m]LaguerreProdIntX12[i,m-{1,0,0},z]-(First[i]+1)LaguerreProdIntX12[i+{1,0,0},m-{1,0,0},z]]

(*(i1!/(i1+m1)! i2!/(i2+m2)! i3!/(i3+m1-m2)!)^(1/2) Integrate[x^m1 LaguerreL[i1,m1,x]LaguerreL[i2,m2,x]LaguerreL[i3,m1-m2,x]Exp[-3x/2],{x,0,\[Infinity]}]*)
HylleraasProdDCoeff[i_List]:=LaguerreProdInt[i,{0,0,0},3/2]
HylleraasProdDCoeff[i_List,{0,0}]:=HylleraasProdDCoeff[i]
HylleraasProdDCoeff[i_List,{m1_,m2_}]:=Sqrt[Times@@(i!)/Times@@((i+{m1,m2,m1-m2})!)]LaguerreProdIntX1[i,{m1,m2,m1-m2},3/2]/;m1>=0\[And]m2>=0

(*(i1!/(i1+m1)! i2!/(i2+m2)! i3!/(i3+m1+m2)!)^(1/2) Integrate[x^(m1+m2) LaguerreL[i1,m1,x]LaguerreL[i2,m2,x]LaguerreL[i3,m1+m2,x]Exp[-3x/2],{x,0,\[Infinity]}]*)
HylleraasProdSCoeff[i_List]:=LaguerreProdInt[i,{0,0,0},3/2]
HylleraasProdSCoeff[i_List,{0,0}]:=HylleraasProdSCoeff[i]
HylleraasProdSCoeff[i_List,{m1_,m2_}]:=Sqrt[Times@@(i!)/Times@@((i+{m1,m2,m1+m2})!)]LaguerreProdIntX12[i,{m1,m2,m1+m2},3/2]/;m1>=0\[And]m2>=0

(* Products of Hylleraas expansions *)

HylleraasProdDMatrix[n_,m_,length1_,length2_]:=HylleraasProdDMatrix[n,m,length1,length2]=Table[HylleraasProdDCoeff[{i,j,n},m],{i,0,length1-1},{j,0,length2-1}]
HylleraasProdSMatrix[n_,m_,length1_,length2_]:=HylleraasProdSMatrix[n,m,length1,length2]=Table[HylleraasProdSCoeff[{i,j,n},m],{i,0,length1-1},{j,0,length2-1}]

HylleraasProdD[d1_,d2_,length_]:=HylleraasProdD[d1,d2,{0,0},length]
HylleraasProdD[d1_,d2_,m_,length_]:=Table[(d1.(HylleraasProdDMatrix[n,m,Length[d1],Length[d2]].d2)),{n,0,length-1}]

HylleraasProdS[d1_,d2_,length_]:=HylleraasProdS[d1,d2,{0,0},length]
HylleraasProdS[d1_,d2_,m_,length_]:=Table[(d1.(HylleraasProdSMatrix[n,m,Length[d1],Length[d2]].d2)),{n,0,length-1}]

(* HylleraasExpansion[d1,m1,p1 x]HylleraasExpansion[d2,m2,p2 x]==HylleraasExpansion[d',m1-m2,1/2(p1+p2)x] *)
HylleraasProdDArgscale[{m1_,p1_,d1_},{m2_,p2_,d2_},length_]:=HylleraasProdDArgscale[{m2,p2,d2},{m1,p1,d1},length]/;m1<m2
HylleraasProdDArgscale[{m1_,p1_,d1_},{m2_,p2_,d2_},length_]:=Module[{q1,q2},
	If[p1==p2,HylleraasProdD[d1,d2,{m1,m2},length],
		{q1,q2}=2{p1,p2}/(p1+p2);
		q1^(m1/2) q2^(m2/2) HylleraasProdD[
			LaguerreArgscaleNorm[m1,q1,Length[d1]].d1,
			LaguerreArgscaleNorm[m2,q2,Length[d2]].d2,
		{m1,m2},length]]]

(* HylleraasExpansion[d1,m1,p1 x]HylleraasExpansion[d2,m2,p2 x]==HylleraasExpansion[d',m1+m2,1/2(p1+p2)x] *)
HylleraasProdSArgscale[{m1_,p1_,d1_},{m2_,p2_,d2_},length_]:=Module[{q1,q2},
	If[p1==p2,HylleraasProdS[d1,d2,{m1,m2},length],
		{q1,q2}=2{p1,p2}/(p1+p2);
		q1^(m1/2) q2^(m2/2) HylleraasProdS[
			LaguerreArgscaleNorm[m1,q1,Length[d1]].d1,
			LaguerreArgscaleNorm[m2,q2,Length[d2]].d2,
		{m1,m2},length]]]

(* assuming exponential decay of the coefficients d1_k and d2_k *)
(*LaguerreProd[d1_,d2_,length_]:=Table[NIntegrate[LaguerreLExpansion[d1,x]LaguerreLExpansion[d2,x]LaguerreL[i,x]Exp[-x/2],{x,0,\[Infinity]}],{i,0,length-1}]*)


(* Multiplication by x *)

LaguerreMultX[length_]:=LaguerreMultX[length]=SparseArray[{{i_,i_}:>(2i-1),{i_,j_}:>-Min[i,j]/;Abs[i-j]==1},length {1,1}]

HylleraasMultX[length_]:=LaguerreMultX[length]
HylleraasMultX[0,length_]:=LaguerreMultX[length]
HylleraasMultX[m_,length_]:=HylleraasMultX[m,length]=SparseArray[{{i_,i_}:>(2i+m-1),{i_,j_}:>-(Min[i,j](Min[i,j]+m))^(1/2)/;Abs[i-j]==1},length {1,1}]

HylleraasMultPoly[m_,cf_List,d_List]:=Module[{X=HylleraasMultX[m,Length[d]]},
	Simplify[cf.NestList[FullSimplify[X.#]&,d,Length[cf]-1]]]

MatrixPoly[cf_List,A_]:=Simplify[cf.NestList[FullSimplify[A.#]&,IdentityMatrix[Length[A]],Length[cf]-1]]


(* Argument rescaling *)

(* Pascal's triangle *)
PascalTrig[length_]:=NestList[#+RotateRight[#]&,UnitVector[length,1],length-1]

(* LaguerreExpansion[d,m,y x] == LaguerreExpansion[d',m,x] *)
LaguerreArgscale[y_,length_]:=LaguerreArgscale[0,y,length]
LaguerreArgscale[m_,0,length_]:=Table[If[i==0,Binomial[j+m,m],0],{i,0,length-1},{j,0,length-1}]
LaguerreArgscale[m_,1,length_]:=IdentityMatrix[length]
LaguerreArgscale[m_,y_,length_]:=Transpose[PascalTrig[length+m][[m+1;;-1,m+1;;-1]]ToeplitzMatrix[(1/y-1)^Range[0,length-1],UnitVector[length,1]](y^Range[0,length-1])]

LaguerreArgscaleNorm[m_,y_,length_]:=Module[{s=Sqrt[#!/(m+#)!]&/@Range[0,length-1]},((# s)&/@LaguerreArgscale[m,y,length])/s]

(* HylleraasExpansion[d,m,y x] == HylleraasExpansion[d',m,x] *)
HylleraasArgscaleCoeff[m_,y_,i_,k_]:=HylleraasArgscaleCoeff[m,y,i,k]=
	Simplify[(2 Sqrt[y]/(1+y))^m 2/(y+1) Sqrt[Binomial[i+m,m]Binomial[k+m,m]] (-1)^k ((y-1)/(y+1))^(i+k) Hypergeometric2F1[-i,-k,1+m,-4y/(y-1)^2],Assumptions->y>0]
HylleraasArgscale[m_,y_,length_]:=Table[HylleraasArgscaleCoeff[m,y,i,k],{i,0,length-1},{k,0,length-1}]


(* Numeric Hylleraas expansions *)

HylleraasH[n_,x_]:=Exp[-x/2] LaguerreL[n,x] (* version for m==0 *)
HylleraasH[n_,0,x_]:=HylleraasH[n,x]
HylleraasH[n_,m_,x_]:=Exp[-x/2]x^(m/2) (Gamma[n+1]/Gamma[n+m+1])^(1/2)LaguerreL[n,m,x]

HylleraasExpansion[d_,x_?NumberQ]:=d.(HylleraasH[#,x]&/@Range[0,Length[d]-1])
HylleraasExpansion[d_,0,x_?NumberQ]:=HylleraasExpansion[d,x]
HylleraasExpansion[d_,m_,x_?NumberQ]:=d.(HylleraasH[#,m,x]&/@Range[0,Length[d]-1])


(* Exponential and ArcCoth integral *)

BinomialDiv[k_,i_,m_,y_]:=BinomialDiv[k,i,m,y]=Binomial[k+m,i+m] HypergeometricPFQ[{1,1,i-k},{1+i,1+i+m},y]

(* Integrate[1/(x+z)LaguerreL[k,m,y x]Exp[-x],{x,0,\[Infinity]}], which is equal to Integrate[1/(x+2z)LaguerreL[k,m,y x/2]Exp[-x/2],{x,0,\[Infinity]}] *)
InvXZLaguerreIntegral[k_,m_,z_,y_]:=InvXZLaguerreIntegral[k,m,z,y]=
	Simplify[LaguerreL[k,m,-y z]Gamma[0,z]Exp[z]-Sum[BinomialDiv[k,i,m,y](y z)^i/i!,{i,1,k}]/z]

(* Integrate[Log[x/z] LaguerreL[k,m,x] Exp[-x],{x,0,\[Infinity]}] *)
LogLaguerreIntegral[k_,m_,z_]:=LogLaguerreIntegral[k,m,z]=
	Simplify[-Binomial[k+m-1,k](EulerGamma+Log[z])+Sum[Binomial[k+m,i+m](-1)^i HarmonicNumber[i],{i,1,k}]]

(* Integrate[Log[x/z] LaguerreL[k,m,y x] Exp[-x],{x,0,\[Infinity]}] *)
LogLaguerreScaledIntegral[k_,m_,z_,1]:=LogLaguerreIntegral[k,m,z] (* need special version for y==1 *)
LogLaguerreScaledIntegral[k_,m_,z_,y_]:=LogLaguerreScaledIntegral[k,m,z,y]=
	Simplify[-Binomial[k+m,k]((1-y)^k+m Sum[Binomial[k,i]y^i (1-y)^(k-i)/(i+m),{i,1,k}])(EulerGamma+Log[z])
		+Sum[Binomial[k+m,i+m](-y)^i HarmonicNumber[i],{i,1,k}]]

(* Integrate[LaguerreL[k,m,x] Exp[-x] 2ArcCoth[1+2x/z],{x,0,\[Infinity]}] *)
ArcCothExpLaguerreIntegral[k_,m_,z_]:=ArcCothExpLaguerreIntegral[k,m,z]=
	Simplify[InvXZLaguerreIntegral[k,m,z,1]-If[k>0,InvXZLaguerreIntegral[k-1,m,z,1],0]-LogLaguerreIntegral[k,m,z]]

(* Integrate[LaguerreL[k,m,y x] Exp[-x] 2ArcCoth[1+2x/z],{x,0,\[Infinity]}] *)
ArcCothExpScaledLaguerreIntegral[k_,m_,z_,1]:=ArcCothExpLaguerreIntegral[k,m,z] (* need special version for y==1 *)
ArcCothExpScaledLaguerreIntegral[k_,m_,z_,y_]:=ArcCothExpScaledLaguerreIntegral[k,m,z,y]=
	Simplify[InvXZLaguerreIntegral[k,m,z,y]-y Sum[(1-y)^(k-1-i) InvXZLaguerreIntegral[i,m,z,y],{i,0,k-1}]-LogLaguerreScaledIntegral[k,m,z,y]]


(* Angular wavefunction (see angular spheroidal wave equation) *)

(* Reference: M. Aubert, N. Bessis, and G. Bessis.
	Prolate-spheroidal orbitals for homonuclear and heteronuclear diatomic molecules. I. Basic procedure.
	Physical Review A, 10:51-60, 1974 *)

(* \[CapitalDelta]q == (Za-Zb) R *)
fnn[n_,m_,p_]:=-n(n+1)+p^2((2n(n+1)-2m^2-1)/((2n+3)(2n-1))-1)
fnn1[n_,m_,\[CapitalDelta]q_]:=-\[CapitalDelta]q Sqrt[(n+m+1)(n-m+1)/((2n+1)(2n+3))] (* heteronuclear case, \[CapitalDelta]q == (Za-Zb)R *)
fnn2[n_,m_,p_]:=p^2/(2n+3) Sqrt[(n+m+1)(n-m+1)(n+m+2)(n-m+2)/((2n+1)(2n+5))]
GenerateF[m_,p_,\[CapitalDelta]q_,length_]:=SparseArray[{
	{i_,i_}:>fnn[i-1+m,m,p], (* zero-based indices *)
	{i_,j_}:>fnn1[Min[i,j]-1+m,m,\[CapitalDelta]q]/;Abs[i-j]==1,
	{i_,j_}:>fnn2[Min[i,j]-1+m,m,p]/;Abs[i-j]==2},
	length {1,1}]
GenerateF[m_,p_,length_]:=GenerateF[m,p,0,length] (* homonuclear case *)

(* homonuclear case *)
AngularCoeff[{l_,m_,p_},length_]:=(*AngularCoeff[{l,m,p},length]=*)
	Module[{c,\[Lambda]=Re[SpheroidalEigenvalue[l,m,I p]],F,s=Mod[l-m,2]}, (* Re only required due to numerical roundoff errors *)
	F=GenerateF[m,p,length]+\[Lambda] SparseArray[{i_,i_}->1,{length,length}];
	c=First[NullSpace[F[[1+s;; ;;2,1+s;; ;;2]],Tolerance->$MachineEpsilon]]; (* only every second Legendre polynomial due to parity *)
	c=Sqrt[2/(2l+1) (l+m)!/(l-m)! / (c.c)]c; (* normalization *)
	c=Riffle[c,0,{2-s,-1-Mod[s+length,2],2}];
	Sign[Re[SpheroidalPS[l,m,I p,3/4]]/LegendreExpansion[m,c,3/4]]c]

 (* heteronuclear case *)

(* "Generalized" spheroidal eigenvalue \[Lambda] with degree n and order m,
	(1-z^2)y''[z]-2z y'[z]+(\[Lambda]-\[CapitalDelta]q z+\[Gamma]^2 (1-z^2)-m^2/(1-z^2))y[z] == 0 *)
GeneralizedSpheroidalEigenvalue[n_,m_,\[Gamma]_,0 ] :=Re[SpheroidalEigenvalue[n,m,\[Gamma]]] (* Re only required due to numerical roundoff errors *)
GeneralizedSpheroidalEigenvalue[n_,m_,\[Gamma]_,0.] :=GeneralizedSpheroidalEigenvalue[n,m,\[Gamma],0]
GeneralizedSpheroidalEigenvalue[n_,m_,\[Gamma]_,\[CapitalDelta]q_]:=RankedMin[-Eigenvalues[Re[N[GenerateF[m,-I \[Gamma],\[CapitalDelta]q,31]]]],n-m+1]

AngularCoeff[lmp_List,0, length_]:=AngularCoeff[lmp,length]
AngularCoeff[lmp_List,0.,length_]:=AngularCoeff[lmp,length]
AngularCoeff[{l_,m_,p_},\[CapitalDelta]q_,length_]:=
	Module[{c,\[Lambda]=GeneralizedSpheroidalEigenvalue[l,m,I p,\[CapitalDelta]q],F},
	F=N[GenerateF[m,p,\[CapitalDelta]q,length]]+\[Lambda] SparseArray[{i_,i_}->1,{length,length}];
	c=First[NullSpace[F,Tolerance->10$MachineEpsilon]];
	c=Sqrt[2/(2l+1) (l+m)!/(l-m)! / (c.c)]c; (* normalization *)
	Sign[Re[SpheroidalPS[l,m,I p,3/4]]/LegendreExpansion[m,c,3/4]]c]

(* Expansion in normalized Legendre polynomials *)
LegendreExpansion[m_,c_,x_]:=c.(Sqrt[(2#+1)/2 (#-m)!/(#+m)!]LegendreP[#,m,x]&/@Range[m,Length[c]+m-1])

(* Multiplication by x:
	x LegendreExpansion[m,c,x] == LegendreExpansion[m,c',x] *)
LegendreMultX[{m_,c_}]:=Module[{s=Sqrt[((#-m)(#+m))/((2#-1)(2#+1))]&/@Range[m,Length[c]+m]},Simplify[Append[(s Append[c,0])[[2;;]],0]+s Prepend[c,0]]]


(* Angular Legendre integrals *)

(* Integrate[SpheroidalPS[l,m,I p,z]]^2,{z,-1,1}]
	just use normalization factor *)
AngularSquareIntegral[{l_,m_}]:=2/(2l+1) (l+m)!/(l-m)!

(* Integrate[(z SpheroidalPS[l,m,I p,z]])^2,{z,-1,1}] *)
AngularSquareX2Integral[{m_,c_}]:=(#.#)&[LegendreMultX[{m,c}]]

AngularSquareIntegralV[{l_,m_,c_}]:={AngularSquareIntegral[{l,m}],-AngularSquareX2Integral[{m,c}]}

ThreeJProd[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=ThreeJProd[{l1,m1},{l2,m2},{l3,m3}]=ThreeJSymbol[{l1,m1},{l2,m2},{l3,m3}]ThreeJSymbol[{l1,0},{l2,0},{l3,0}]

(* Gaunt's integral for m1,m2,m3>=0:
	1/2 Sqrt[(l1-m1)!/(l1+m1)! (l2-m2)!/(l2+m2)! (l3-m3)!/(l3+m3)!] Integrate[LegendreP[l1,m1,z] LegendreP[l2,m2,z] LegendreP[l3,m3,z],{z,-1,1}] *)
LegendreProdIntegral[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=0/;Abs[l1-l2]>l3\[Or]l3>l1+l2
LegendreProdIntegral[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=LegendreProdIntegral[{l2,m2},{l1,m1},{l3,m3}]/;m1<m2
LegendreProdIntegral[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=(-1)^(m2+m3) ThreeJProd[{l1,m1},{l2,-m2},{l3,-m3}]/;m3==Abs[m1-m2]
LegendreProdIntegral[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=(-1)^m3 ThreeJProd[{l1,m1},{l2,m2},{l3,-m3}]/;m3==m1+m2
LegendreProdIntegral[{l1_,m1_},{l2_,m2_},{l3_,m3_}]:=0

(* 1/2 Sqrt[(l1-m1)!/(l1+m1)! (l2-m2)!/(l2+m2)! (l3-m3)!/(l3+m3)!] Integrate[LegendreP[l1,m1,z] LegendreP[l2,m2,z] LegendreP[l3,m3,z] z^2,{z,-1,1}] *)
LegendreProdX2Integral[lm1_,lm2_,{l_,m_}]:=LegendreProdX2Integral[lm1,lm2,{l,m}]=Simplify[
	Sqrt[(l+1+m)(l+1-m)(l+2-m)(l+2+m)]/((2l+1)(2l+3))LegendreProdIntegral[lm1,lm2,{l+2,m}]+
	(2l(l+1)-1-2m^2)/((2l-1)(2l+3))LegendreProdIntegral[lm1,lm2,{l,m}]+
	If[l-2>=m,Sqrt[(l-1-m)(l-1+m)(l-m)(l+m)]/((2l-1)(2l+1))LegendreProdIntegral[lm1,lm2,{l-2,m}],0]]

(* Sqrt[(2l1+1)/2] Sqrt[(2l2+1)/2] 2LegendreProdIntegral[{l1,m1},{l2,m2},{\[Tau],\[Nu]}] *)
AngularLegendreIntegralMatrix[m1_,m2_,{\[Tau]_,\[Nu]_},length_]:=AngularLegendreIntegralMatrix[m1,m2,{\[Tau],\[Nu]},length]=
	SparseArray[{i_,j_}:>Sqrt[2(i-1+m1)+1]Sqrt[2(j-1+m2)+1]LegendreProdIntegral[{i-1+m1,m1},{j-1+m2,m2},{\[Tau],\[Nu]}],length{1,1}]

(* Sqrt[(2l1+1)/2] Sqrt[(2l2+1)/2] 2LegendreProdX2Integral[{l1,m1},{l2,m2},{\[Tau],\[Nu]}] *)
AngularLegendreX2IntegralMatrix[m1_,m2_,{\[Tau]_,\[Nu]_},length_]:=AngularLegendreX2IntegralMatrix[m1,m2,{\[Tau],\[Nu]},length]=
	SparseArray[{i_,j_}:>Sqrt[2(i-1+m1)+1]Sqrt[2(j-1+m2)+1]LegendreProdX2Integral[{i-1+m1,m1},{j-1+m2,m2},{\[Tau],\[Nu]}],length{1,1}]

(* Integrate[SpheroidalPS[l1,m1,I p1,z] SpheroidalPS[l2,m2,I p2,z] Sqrt[(\[Tau]-\[Nu])!/(\[Tau]+\[Nu])!]LegendreP[\[Tau],\[Nu],z],{z,-1,1}] *)
(*AngularLegendreIntegral[{l1_,m1_,c1_},{l2_,m2_,c2_},{\[Tau]_,\[Nu]_}]:=If[EvenQ[l1+m1+l2+m2+\[Tau]+\[Nu]],c1.(AngularLegendreIntegralMatrix[m1,m2,{\[Tau],\[Nu]},Length[c2]].c2),0] (* EvenQ: homonuclear case *)*)
AngularLegendreIntegral[{_,m1_,c1_},{_,m2_,c2_},{\[Tau]_,\[Nu]_}]:=c1.(AngularLegendreIntegralMatrix[m1,m2,{\[Tau],\[Nu]},Length[c2]].c2)

(* Integrate[SpheroidalPS[l1,m1,I p1,z] SpheroidalPS[l2,m2,I p2,z] Sqrt[(\[Tau]-\[Nu])!/(\[Tau]+\[Nu])!]LegendreP[\[Tau],\[Nu],z] z^2,{z,-1,1}] 
	cannot use LegendreMultX[{m1,c1}] and LegendreMultX[{m2,c2}], otherwise 'ThreeJSymbol' "is not physical" any more *)
(*AngularLegendreX2Integral[{l1_,m1_,c1_},{l2_,m2_,c2_},{\[Tau]_,\[Nu]_}]:=If[EvenQ[l1+m1+l2+m2+\[Tau]+\[Nu]],c1.(AngularLegendreX2IntegralMatrix[m1,m2,{\[Tau],\[Nu]},Length[c2]].c2),0] (* EvenQ: homonuclear case *)*)
AngularLegendreX2Integral[{_,m1_,c1_},{_,m2_,c2_},{\[Tau]_,\[Nu]_}]:=c1.(AngularLegendreX2IntegralMatrix[m1,m2,{\[Tau],\[Nu]},Length[c2]].c2)

AngularLegendreIntegralV[i1_,i2_,\[Tau]\[Nu]_]:={AngularLegendreIntegral[i1,i2,\[Tau]\[Nu]],-AngularLegendreX2Integral[i1,i2,\[Tau]\[Nu]]}
(*AngularLegendreIntegralV[i1_,i2_,\[Tau]\[Nu]_]:=Module[{ret},Print["AngularLegendreIntegralV called..."];ret={AngularLegendreIntegral[i1,i2,\[Tau]\[Nu]],-AngularLegendreX2Integral[i1,i2,\[Tau]\[Nu]]};Print["AngularLegendreIntegralV done."];ret]*)


(* Reference implementation of angular Legendre integrals *)

(* Integrate[SpheroidalPS[l,m,I p,z]]^2 z^j,{z,-1,1}] *)
AngularSquareIntegralN[{l_,m_,p_},j_]:=AngularSquareIntegralN[{l,m,p},j]=If[EvenQ[j],NIntegrate[Re[SpheroidalPS[l,m,I p,z]]^2 z^j,{z,-1,1}],0]

(* Integrate[SpheroidalPS[l1,m1,I p1,z] SpheroidalPS[l2,m2,I p2,z] z^j,{z,-1,1}] *)
AngularIntegralN[{l1_,m1_,p1_},{l2_,m2_,p2_},j_]:=AngularIntegralN[{l1,m1,p1},{l2,m2,p2},j]=
	If[EvenQ[l1+m1+l2+m2+j],NIntegrate[Re[SpheroidalPS[l1,m1,I p1,z]]Re[SpheroidalPS[l2,m2,I p2,z]]z^j,{z,-1,1}],0]

AngularIntegralVN[i1_,i2_]:={AngularIntegralN[i1,i2,0],-AngularIntegralN[i1,i2,2]}

(* Integrate[SpheroidalPS[l1,m1,I p1,z] SpheroidalPS[l2,m2,I p2,z] Sqrt[(\[Tau]-\[Nu])!/(\[Tau]+\[Nu])!]LegendreP[\[Tau],\[Nu],z] z^j,{z,-1,1}] *)
AngularLegendreIntegralN[{l1_,m1_,p1_},{l2_,m2_,p2_},{\[Tau]_,\[Nu]_},j_]:=AngularLegendreIntegralN[{l1,m1,p1},{l2,m2,p2},{\[Tau],\[Nu]},j]=
	If[EvenQ[l1+m1+l2+m2+\[Tau]+\[Nu]+j],Sqrt[(\[Tau]-\[Nu])!/(\[Tau]+\[Nu])!]NIntegrate[Re[SpheroidalPS[l1,m1,I p1,z]]Re[SpheroidalPS[l2,m2,I p2,z]]LegendreP[\[Tau],\[Nu],z]z^j,{z,-1,1}],0]

AngularLegendreIntegralVN[i1_,i2_,\[Tau]\[Nu]_]:={AngularLegendreIntegralN[i1,i2,\[Tau]\[Nu],0],-AngularLegendreIntegralN[i1,i2,\[Tau]\[Nu],2]}
(*AngularLegendreIntegralVN[i1_,i2_,\[Tau]\[Nu]_]:=Module[{r},Print["AngularLegendreIntegralVN called..."];r={AngularLegendreIntegralN[i1,i2,\[Tau]\[Nu],0],-AngularLegendreIntegralN[i1,i2,\[Tau]\[Nu],2]};Print["AngularLegendreIntegral done."];r]*)


(* Radial wavefunction (Laguerre expansion) *)

(* Reference: M. Aubert, N. Bessis, and G. Bessis.
	Prolate-spheroidal orbitals for homonuclear and heteronuclear diatomic molecules. I. Basic procedure.
	Physical Review A, 10:51-60, 1974 *)

(* q == 2 Z R *)
qnn[n_,m_,p_,q_]:=(2n+1)(q/(2p)-n-1-2p)+m^2/4+n+q
qnn1[n_,m_,p_,q_]:=-((n-m/2+1)(n+m/2+1))^(1/2)(q/(2p)-n-1)
GenerateQ[m_,p_,q_,length_]:=SparseArray[{
	{i_,i_}:>qnn[i-1+m/2,m,p,q], (* zero-based indices *)
	{i_,j_}:>qnn1[Min[i,j]-1+m/2,m,p,q]/;Abs[i-j]==1},
	length {1,1}]

bnn[n_,p_]:=4p+2n+1
bnn1[n_,m_]:=-((n-m/2+1)(n+m/2+1))^(1/2)
GenerateB[m_,p_,length_]:=SparseArray[{
	{i_,i_}:>bnn[i-1+m/2,p],
	{i_,j_}:>bnn1[Min[i,j]-1+m/2,m]/;Abs[i-j]==1},
	length {1,1}]

RadialY[{l_,   p_},{q_,\[CapitalDelta]q_},length_]:=GenerateQ[0,p,q,length]-GeneralizedSpheroidalEigenvalue[l,0,I p,\[CapitalDelta]q]SparseArray[{i_,i_}->1,{length,length}] (* version for m==0 *)
RadialY[{l_,0, p_},{q_,\[CapitalDelta]q_},length_]:=RadialY[{l,p},{q,\[CapitalDelta]q},length]
RadialY[{l_,m_,p_},{q_,\[CapitalDelta]q_},length_]:=Module[{
	Q=GenerateQ[m,p,q,length]-GeneralizedSpheroidalEigenvalue[l,m,I p,\[CapitalDelta]q]SparseArray[{i_,i_}->1,{length,length}],
	B=GenerateB[m,p,length]},
		B.Q+p m^2 IdentityMatrix[length]]

(* p should be a root of the following function *)
RadialPZero[{l_,p_?NumberQ},q_,length_]:=Nearest[Eigenvalues[RadialY[{l,p},q,length]],0] (* version for m==0 *)
RadialPZero[{l_,0,p_?NumberQ},q_,length_]:=RadialPZero[{l,p},q,length]
RadialPZero[{l_,m_,p_?NumberQ},q_,length_]:=Nearest[Eigenvalues[RadialY[{l,m,p},q,length]],0]

CalculateP[{l_,m_},pstart_,q_]:=p/.FindRoot[RadialPZero[{l,m,p},q,31],{p,pstart},WorkingPrecision->20,AccuracyGoal->MachinePrecision]

(* Dynamic programming: store calculated results *)
RadialCoeff[{l_,p_},q_,length_]:=RadialCoeff[{l,p},q,length]=First[NullSpace[Normal[RadialY[{l,p},q,length]],Tolerance->10^-11]] (* version for m==0 *)
RadialCoeff[{l_,0,p_},q_,length_]:=RadialCoeff[{l,p},q,length]
RadialCoeff[{l_,m_,p_},q_,length_]:=RadialCoeff[{l,m,p},q,length]=First[NullSpace[Normal[RadialY[{l,m,p},q,length]],Tolerance->10^-11]]


(* Normalization factor; 'c' and 'd' are the angular and radial expansion coefficients, respectively *)
NormFactor[{l_,m_,p_,c_,d_}]:=Module[{
	a=AngularSquareIntegralV[{l,m,c}],
	X=HylleraasMultX[m,Length[d]],X1d},
	X1d=d+X.d/(2p);
	Sqrt[\[Pi]/p {X1d.X1d,d.d}.a]]/;m>=0



(* {{n,l,m,{p-fit slope,p-fit offset},numRadCoeffs},...} *)
ParaInfo[\[CapitalDelta]Zrel_]:={
{(*1s\[Sigma]*)1,0,0, 1/2 {1+\[CapitalDelta]Zrel/2,1},19},
{(*1p\[Sigma]*)1,1,0, 1/2 {1-\[CapitalDelta]Zrel/2,1},19},
{(*2s\[Sigma]*)2,0,0, 1/4 {1+\[CapitalDelta]Zrel/2,3},23},
{(*2p\[Sigma]*)2,1,0, 1/4 {1-\[CapitalDelta]Zrel/2,4},26},
{(*1d\[Sigma]*)1,2,0, 1/4 {1+\[CapitalDelta]Zrel/2,3},22},
{(*1p\[Pi]*)1,1,1, 1/4 {1+\[CapitalDelta]Zrel/2,3},22},{(*1p(-\[Pi])*)1,1,-1, 1/4 {1+\[CapitalDelta]Zrel/2,3},22},
{(*1d\[Pi]*)1,2,1, 1/4 {1-\[CapitalDelta]Zrel/2,5},25},{(*1d(-\[Pi])*)1,2,-1, 1/4 {1-\[CapitalDelta]Zrel/2,5},25},
{(*1f\[Sigma]*)1,3,0, 1/4 {1-\[CapitalDelta]Zrel/2,5},22},
{(*3s\[Sigma]*)3,0,0, 1/6 {1+\[CapitalDelta]Zrel/2,6},30},
{(*2p\[Pi]*)2,1,1, 1/6 {1+\[CapitalDelta]Zrel/2,6},25},{(*2p(-\[Pi])*)2,1,-1, 1/6 {1+\[CapitalDelta]Zrel/2,6},25}};

(* return format: {{l,m,p,c(angular coeffs),d(radial coeffs)},...} *)
OrbitalParameters[q_,paraInfo_]:=Module[{p},
	(p=CalculateP[{#[[2]],Abs[#[[3]]]},#[[4,1]]First[q]/2+#[[4,2]],q];{#[[2]],#[[3]],p,AngularCoeff[{#[[2]],Abs[#[[3]]],p},Last[q],31],RadialCoeff[{#[[2]],Abs[#[[3]]],p},q,#[[5]]]})&/@paraInfo]

(* single-electron energy *)
EnergySingle[Z_,q_,orbParams_,\[Rho]1_]:=Module[{h=DiagonalMatrix[-2 (Z #/(First[q]/2))^2&/@orbParams[[All,3]]]},Outer[Tr[h.#]&,\[Rho]1,2]]


(* Radial Laguerre integrals including ArcCoth[1+x/z] *)

(*RadialLegendrePIntegral[k_,\[Tau]_,m_,z_,x_]:=RadialLegendrePIntegral[k,\[Tau],m,z,x]=
	Integrate[y^(m/2)LaguerreL[k,m,y]Exp[-y/2]LegendreP3[\[Tau],m,1+y/z],{y,0,x},Assumptions->{x>0,z>0}]*)

RadialLaguerreIntegralCoeff[m_,k1_,k2_,j_]:=LaguerreProdInt[{k1,k2,j},{m,m,0},1]+2Sum[(-1)^(k1-i) LaguerreProdInt[{i,k2,j},{m,m,0},1],{i,Max[0,j-k2],k1-1}]

(* Integrate[LaguerreL[k2,x]Exp[-x/2]ArcCoth[1+x/z]Integrate[LaguerreL[k1,x1]Exp[-x1/2],{x1,0,x}],{x,0,\[Infinity]}] *)
RadialLaguerreIntegral[z_,k1_,k2_]:=RadialLaguerreIntegral[z,k1,k2]=
	Simplify[2(-1)^k1 ArcCothExpScaledLaguerreIntegral[k2,0,z,2]-Sum[RadialLaguerreIntegralCoeff[0,k1,k2,j]ArcCothExpLaguerreIntegral[j,0,2z],{j,0,k1+k2}],Assumptions->z>0]

(* Sqrt[k1!/(k1+m)! k2!/(k2+m)!] Integrate[LaguerreL[k2,m,x]Exp[-x/2]ArcCoth[1+x/z]Integrate[LaguerreL[k1,m,x1]Exp[-x1/2],{x1,0,x}],{x,0,\[Infinity]}] *)
RadialLaguerreIntegral[z_,0,k1_,k2_]:=RadialLaguerreIntegral[z,k1,k2]
RadialLaguerreIntegral[z_,m_,k1_,k2_]:=RadialLaguerreIntegral[z,m,k1,k2]=
	Sqrt[k1!/(k1+m)! k2!/(k2+m)!]Simplify[2((-1)^k1+Sum[(-1)^(k1-1-i)Binomial[i+m,m-1],{i,0,k1-1}]) ArcCothExpScaledLaguerreIntegral[k2,m,z,2]
		-Sum[RadialLaguerreIntegralCoeff[m,k1,k2,j]ArcCothExpLaguerreIntegral[j,0,2z],{j,0,k1+k2}],Assumptions->z>0]

(* Sqrt[k1!/(k1+m)! k2!/(k2+m)!] Integrate[1/(x+2z)LaguerreL[k2,m,x]Exp[-x/2]Integrate[LaguerreL[k1,m,x1]Exp[-x1/2],{x1,0,x}],{x,0,\[Infinity]}] *)
RadialInvXZLaguerreIntegral[z_,m_,k1_,k2_]:=RadialInvXZLaguerreIntegral[z,m,k1,k2]=
	Sqrt[k1!/(k1+m)! k2!/(k2+m)!]Simplify[2((-1)^k1+Sum[(-1)^(k1-1-i)Binomial[i+m,m-1],{i,0,k1-1}]) InvXZLaguerreIntegral[k2,m,z,2]
		-Sum[RadialLaguerreIntegralCoeff[m,k1,k2,j] 2InvXZLaguerreIntegral[j,0,2z,1],{j,0,k1+k2}],Assumptions->z>0]


(* Nested Laguerre exponential integrals *)

(* 1/2 Integrate[LaguerreL[k2,m,x]Exp[-x/2]Integrate[LaguerreL[k1,m,y]Exp[-y/2],{y,0,x}],{x,0,\[Infinity]}] *)
NestedLaguerreExpIntTable[0,length_]:=IdentityMatrix[length]+2Table[(-1)^(k1+k2) If[k2>k1,1,0],{k1,0,length-1},{k2,0,length-1}]
NestedLaguerreExpIntTable[1,length_]:=Table[If[k1<=k2,(-1)^k2 Mod[k1+1,2],Mod[k2+1,2]],{k1,0,length-1},{k2,0,length-1}]

(* Multiply each entry by the normalization factor Sqrt[k1!/(k1+m)! k2!/(k2+m)!] *)
NestedLaguerreNormExpIntTable[m_,length_]:=Table[Sqrt[k1!/(k1+m)!k2!/(k2+m)!],{k1,0,length-1},{k2,0,length-1}]NestedLaguerreExpIntTable[m,length]


(* Matrix representation to multiply a Hylleraas expansion by LegendreP3[\[Tau],\[Nu],1+x/z] or LegendreQ3[\[Tau],\[Nu],1+x/z] *)

(* m==0 *)
LegendrePCoeffsEven[z_,\[Tau]_,length_]:=Module[{clist=CoefficientList[LegendreP3[\[Tau],1+x/z],x]},MatrixPoly[clist,LaguerreMultX[length]][[All,1;;length-Length[clist]+1]]]
LegendreQCoeffsEven0[z_,0,length_]:=ConstantArray[0,{length,length}]
LegendreQCoeffsEven0[z_,\[Tau]_,length_]:=Module[{clist=CoefficientList[Coefficient[LegendreQ3[\[Tau],1+x/z],ArcCoth[1+x/z],0],x]},MatrixPoly[clist,LaguerreMultX[length]][[All,1;;length-Length[clist]+1]]]

(* m odd *)
LegendreP3PolyOdd [\[Tau]_,m_,x_,z_]:=FullSimplify[Sqrt[2z+x] x^(m/2) LegendreP3[\[Tau],m,1+x/z],Assumptions->{x>0,z>1}]
LegendreQ3PolyOdd0[\[Tau]_,m_,x_,z_]:=FullSimplify[(2z+x)^(m/2) x^(m/2) Coefficient[LegendreQ3[\[Tau],m,1+x/z],ArcCoth[1+x/z],0],Assumptions->{x>0,z>1}] (* need factor (2z+x)^(m/2) to obtain a polynomial *)
LegendreQ3PolyOdd1[\[Tau]_,m_,x_,z_]:=FullSimplify[(2z+x)^(m/2) x^(m/2) Coefficient[LegendreQ3[\[Tau],m,1+x/z],ArcCoth[1+x/z],1],Assumptions->{x>0,z>1}]

LegendrePCoeffsOdd [z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreP3PolyOdd [\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;OddQ[m]\[And]\[Tau]>=m
LegendreQCoeffsOdd0[z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreQ3PolyOdd0[\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;OddQ[m]\[And]\[Tau]>=m
LegendreQCoeffsOdd1[z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreQ3PolyOdd1[\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;OddQ[m]\[And]\[Tau]>=m

(* m even, m>=2 *)
LegendreP3PolyEven [\[Tau]_,m_,x_,z_]:=FullSimplify[x^(m/2)LegendreP3[\[Tau],m,1+x/z],Assumptions->{x>0,z>1}]
LegendreQ3PolyEven0[\[Tau]_,m_,x_,z_]:=FullSimplify[x^(m/2)Coefficient[LegendreQ3[\[Tau],m,1+x/z],ArcCoth[1+x/z],0](x+2z)^(m/2),Assumptions->{x>0,z>1}] (* need factor (x+2z)^(m/2) to obtain a polynomial *)
LegendreQ3PolyEven1[\[Tau]_,m_,x_,z_]:=FullSimplify[x^(m/2)Coefficient[LegendreQ3[\[Tau],m,1+x/z],ArcCoth[1+x/z],1],Assumptions->{x>0,z>1}]

LegendrePCoeffsEven [z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreP3PolyEven [\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;EvenQ[m]\[And]\[Tau]>=m
LegendreQCoeffsEven0[z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreQ3PolyEven0[\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;EvenQ[m]\[And]\[Tau]>=m
LegendreQCoeffsEven1[z_,\[Tau]_,m_,length_]:=Module[{clist=CoefficientList[LegendreQ3PolyEven1[\[Tau],m,x,z],x]},MatrixPoly[clist,HylleraasMultX[m,length]][[All,1;;length-Length[clist]+1]]]/;EvenQ[m]\[And]\[Tau]>=m


(* Hylleraas expansion of 1/Sqrt[2z+x] HylleraasH[k,m,x] *)

(* Integrate[1/Sqrt[2z+x] LaguerreL[k,x]Exp[-x],{x,0,\[Infinity]}]
	using dynamic programming and recurrence relations *)
SqrtIntLaguerre[0,z_]:=Sqrt[\[Pi]]Erfc[Sqrt[2z]]Exp[2z]
SqrtIntLaguerre[k_,z_]:=SqrtIntLaguerre[k,z]=Simplify[SqrtIntLaguerre[k-1,z]+z Sqrt[z]D[SqrtIntLaguerre[k-1,z]/Sqrt[z],z]/k,Assumptions->z>0]

(* Integrate[1/Sqrt[2z+x] HylleraasH[k1,m,x]HylleraasH[k2,m,x],{x,0,\[Infinity]}] *)
SqrtHylleraasExpansion[m_,k1_,k2_]:=SqrtHylleraasExpansion[m,k1,k2]=
	Simplify[Sqrt[k1!/(k1+m)!k2!/(k2+m)!]Sum[LaguerreProdIntX1[{k1,k2,i},{m,m,0},1]SqrtIntLaguerre[i,z],{i,0,k1+k2+m}],Assumptions->z>0]


(* Coulomb integral using Neumann's expansion *)

RadialCoulombIntegral[\[Nu]_,{p1_,d1_},{p2_,d2_},z0_,inttable_]:=
	Module[{z,zp,c1,c2,s1,s2},
		z=p1+p2;
		(*Print["z: ",z,", \[Nu]: ",\[Nu],", p1: ",p1,", p2: ",p2];*)
		If[p1!=p2,
			c1=HylleraasArgscale[\[Nu],2p1/z,Length[d1]].d1;
			c2=HylleraasArgscale[\[Nu],2p2/z,Length[d2]].d2,
			c1=d1;c2=d2];
		(*{{m1,p1,d1},{m2,p2,d2},{m1,z/2,c1},{m2,z/2,c2}}*)
		(* multiplication by \[Xi]^2=(1+x/z)^2, invalidates 2 trailing coefficients *)
		s1=HylleraasMultPoly[\[Nu],{1,2/z,1/z^2},c1][[;;-3]];
		s2=HylleraasMultPoly[\[Nu],{1,2/z,1/z^2},c2][[;;-3]];
		c1=c1[[;;-3]];
		c2=c2[[;;-3]];
		zp=(z-z0)^Range[0,Length[inttable[[1]]]-1];
		{{s1.#.s2,s1.#.c2},{c1.#.s2,c1.#.c2}}/z^2&/@(zp.#&/@inttable)]


AngInfo[{l_,m_,p_,c_,d_}]:={l,Abs[m],c}

RadialProd[{_,m1_,p1_,_,d1_},{_,m2_,p2_,_,d2_},length_]:={(p1+p2)/2,HylleraasProdDArgscale[{Abs[m1],p1,d1},{Abs[m2],p2,d2},length]}/;(m1 m2)>=0
RadialProd[{_,m1_,p1_,_,d1_},{_,m2_,p2_,_,d2_},length_]:={(p1+p2)/2,HylleraasProdSArgscale[{Abs[m1],p1,d1},{Abs[m2],p2,d2},length]}/;(m1 m2)<0

(* {l,m,p,c,d} *)
CoulombDiatomic[{_,m1_,_,_,_},{_,m2_,_,_,_},{_,m3_,_,_,_},{_,m4_,_,_,_},_,_]:=0/;m1-m2!=-(m3-m4)
CoulombDiatomic[i1_,i2_,i3_,i4_,R_,radIntTables_]:=Module[{\[Nu]=Abs[i1[[2]]-i2[[2]]],z=2Mean[#[[3]]&/@{i1,i2,i3,i4}],z0,it,rci},
	{z0,it}=First[Nearest[radIntTables[[\[Nu]+1]],z]];
	If[Abs[z-z0]>1/4,Print["\[Nu]: ",\[Nu],", z: ",z,", z0: ",z0,", |z-z0|: ",Abs[z-z0]]];
	rci=RadialCoulombIntegral[\[Nu],RadialProd[i1,i2,Length[it[[1,1]]]+2],RadialProd[i3,i4,Length[it[[1,1]]]+2],z0,it];
	(4\[Pi])^2/R (-1)^\[Nu] Sum[(2\[Tau]+1)/2 (AngularLegendreIntegralV[AngInfo[i1],AngInfo[i2],{\[Tau],\[Nu]}].rci[[\[Tau]+1]].AngularLegendreIntegralV[AngInfo[i3],AngInfo[i4],{\[Tau],\[Nu]}]),{\[Tau],\[Nu],Length[it]-1}]]

AbsM[{l_,m_,p_,c_,d_}]:={l,Abs[m],p,c,d}
EvaluateCoulombIntegrals[R_,orbParams_,coullist_,rit_]:=Module[{normfac=NormFactor[AbsM[#]]&/@orbParams},
	SparseArray[({#1,#2,#3,#4}->CoulombDiatomic[orbParams[[#1]],orbParams[[#2]],orbParams[[#3]],orbParams[[#4]],R,rit]/(normfac[[#1]]normfac[[#2]]normfac[[#3]]normfac[[#4]]))&@@#&/@coullist,Length[orbParams]{1,1,1,1},NC]]


(* Reference implementation using NIntegrate *)

(* Radial wavefunction *)
RadialWavefunction[{m_,p_,d_},\[Xi]_?NumberQ]:=HylleraasExpansion[d,m,2p(\[Xi]-1)]

RadialWavefunctionIntegralN[i1_,i2_,j_]:=RadialWavefunctionIntegralN[i1,i2,j]=NIntegrate[RadialWavefunction[i1,\[Xi]]RadialWavefunction[i2,\[Xi]]\[Xi]^j,{\[Xi],1,\[Infinity]}]
RadialWavefunctionIntegralN[i1_,i2_]:={RadialWavefunctionIntegralN[i1,i2,2],RadialWavefunctionIntegralN[i1,i2,0]}

RadialLegendreIntegralN[i1_,i2_,{\[Tau]_,\[Nu]_},j_,\[Chi]_?NumberQ]:=NIntegrate[RadialWavefunction[i1,\[Xi]]RadialWavefunction[i2,\[Xi]]LegendreP[\[Tau],\[Nu],3,\[Xi]]\[Xi]^j,{\[Xi],1,\[Chi]}(*,PrecisionGoal->MachinePrecision*)]

RadialCoulombIntegralN[i1_,i2_,i3_,i4_,{\[Tau]_,\[Nu]_},j1_,j2_]:=RadialCoulombIntegralN[i1,i2,i3,i4,{\[Tau],\[Nu]},j1,j2]=
	(\[Tau]-\[Nu])!/(\[Tau]+\[Nu])!NIntegrate[RadialWavefunction[i3,\[Chi]]RadialWavefunction[i4,\[Chi]]LegendreQ[\[Tau],\[Nu],3,\[Chi]]\[Chi]^j2 RadialLegendreIntegralN[i1,i2,{\[Tau],\[Nu]},j1,\[Chi]],{\[Chi],1,\[Infinity]},Method->"DoubleExponential",PrecisionGoal->(*MachinePrecision*)12]

RadialCoulombIntegralM[i1_,i2_,i3_,i4_,\[Tau]\[Nu]_]:=Outer[RadialCoulombIntegralN[i1,i2,i3,i4,\[Tau]\[Nu],#1,#2]+RadialCoulombIntegralN[i3,i4,i1,i2,\[Tau]\[Nu],#2,#1]&,{2,0},{2,0}]


(* Reference implementation using NIntegrate *)

AngInfoN[{l_,m_,p_,d_}]:={l,Abs[m],p}
RadInfoN[{l_,m_,p_,d_}]:={Abs[m],p,d}

(* {l,m,p,d} *)
CoulombDiatomicN[{_,m1_,_,_},{_,m2_,_,_},{_,m3_,_,_},{_,m4_,_,_},_,_]:=0/;m1-m2!=-(m3-m4)
CoulombDiatomicN[i1_,i2_,i3_,i4_,R_,\[Tau]max_]:=Module[{\[Nu]=Abs[i1[[2]]-i2[[2]]]},
	(2\[Pi])^2 4/R (-1)^\[Nu] Sum(*Table*)[(2\[Tau]+1)/2 If[True(*EvenQ[i1[[1]]+i2[[1]]+\[Tau]] homonuclear case only*),
		AngularLegendreIntegralVN[AngInfoN[i1],AngInfoN[i2],{\[Tau],\[Nu]}].RadialCoulombIntegralM[RadInfoN[i1],RadInfoN[i2],RadInfoN[i3],RadInfoN[i4],{\[Tau],\[Nu]}].AngularLegendreIntegralVN[AngInfoN[i3],AngInfoN[i4],{\[Tau],\[Nu]}],0],{\[Tau],\[Nu],\[Tau]max}]]


(* Legendre function of the first kind, type 3 *)
LegendreP3Sym[n_,x_]:=LegendreP3Sym[n,x]=FullSimplify[LegendreP[n,0,3,x],Assumptions->x>1]
LegendreP3Sym[n_,m_,x_]:=LegendreP3Sym[n,m,x]=FullSimplify[LegendreP[n,m,3,x],Assumptions->x>1]

LegendreP3[n_,x_]:=LegendreP3Sym[n,y]/.{y->x}
LegendreP3[n_,m_,x_]:=LegendreP3Sym[n,m,y]/.{y->x}

(* Legendre function of the second kind, type 3 *)
LegendreQ3Sym[n_,x_]:=LegendreQ3Sym[n,x]=
	FullSimplify[FullSimplify[FunctionExpand[LegendreQ[n,0,3,x]],Assumptions->x>1]/.
		{Log[(1+x)/(-1+x)]->2 ArcCoth[x],Log[(-1+x)/(1+x)]->-2 ArcCoth[x]}];

LegendreQ3Sym[n_,m_,x_]:=LegendreQ3Sym[n,m,x]=
	FullSimplify[FullSimplify[FunctionExpand[LegendreQ[n,m,3,x]],Assumptions->x>1]/.
		{Log[(1+x)/(-1+x)]->2 ArcCoth[x],Log[(-1+x)/(1+x)]->-2 ArcCoth[x]}];

LegendreQ3[n_,x_]:=LegendreQ3Sym[n,y]/.{y->x}
LegendreQ3[n_,m_,x_]:=LegendreQ3Sym[n,m,y]/.{y->x}


(* Utility display functions *)

QuantNumbersToString[{n_,l_,m_}]:=Module[{Lnames={"s","p","d","f","g"},Mnames={"\[Sigma]","\[Pi]","\[Delta]","\[Phi]","\[Gamma]"}},
	ToString[n]<>Lnames[[l+1]]<>If[m==0,First[Mnames],"("<>If[m>0,"+","-"]<>Mnames[[Abs[m]+1]]<>")"]]
