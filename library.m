// Rnd
// INPUT: a field Q
// OUPUT: a random non zero element of Q

Rnd := function(Q)
 if Characteristic(Q) eq 0 then
  rd:=Random(Q,10);
  if rd eq 0 then
   rd:=1;
  end if;
  return rd;
 end if;
 rd:=Random(Q);
 if rd eq 0 then
  rd:=1;
 end if;
 return rd;
end function;


// SequencesofGivenSize
// INPUT: a positive integer n
// OUPUT: a sequence containing the sequences of integers 1,..,n in all possible orders

SequencesofGivenSize := function(n)
 a := {1..n};
 seqs := {}; 
 while #seqs ne Factorial(n) do
  a := {1..n};
  seq := [];
  while a ne {} do
   x := Random(a);
   Append(~seq,x);
   Exclude(~a, x);
  end while;
  Include(~seqs,seq);
 end while;
 return Sort([s: s in seqs]);
end function;


// LinRelPols
// INPUT: a sequence of polynomials S
// OUTPUT: the linear relations of 
// the elements of S

LinRelPols := function(S)
  mm := {};
  for p in S do
   mm := mm join Set(Monomials(p));
  end for;
  mm := Sort(Setseq(mm));
  M := Matrix([[MonomialCoefficient(f,m) : m in mm] : f in S]);
  return Basis(Kernel(M));
end function;

// Hder
// INPUT: a polynomial f, a vector v
// OUTPUT: the derivative of f specified by the vector of exponents v

Hder := function(f,v)
  R := Parent(f);
  Z := ToricLattice(Rank(R));
  cf,mon := CoefficientsAndMonomials(f);
  exp := [Z!Exponents(m) : m in mon];
  g := R!0;
  for i in [1..#exp] do
   e := exp[i]-Z!v;
   if Min(Eltseq(e)) ge 0
    then
     m := Monomial(R,Eltseq(e));
     c := &*[Binomial(Eltseq(exp[i])[j],v[j])*(Factorial(v[j])) : j in
[1..#v]]*cf[i];
     g := g + c*m;
   end if;
  end for;
  return g;
end function;


// ParamLin
// INPUT: a linear space V
// OUTPUT: a parametrization for V

ParamLin := function(V)
 P2 := Ambient(V);
 n2 := Dimension(P2);
 M := Matrix([[MonomialCoefficient(f,P2.i) : i in [1..n2+1]] : f in Equations(V)]);
 B := Basis(Kernel(Transpose(M)));
 ll := [Eltseq(v) : v in Rows(Transpose(Matrix(B)))];
 Q := BaseRing(P2);
 P1 := ProjectiveSpace(Q,Dimension(V));
 return map<P1->P2| [&+[v[i]*P1.i : i in [1..#v]] : v in ll]>;
end function;


// Fiber
// INPUT: a function f, a scheme Z
// OUTPUT: the preimage of Z via f

Fiber := function(f,Z)
   equ := DefiningEquations(f);
   bas := MinimalBasis(Z);
   P := Domain(f);
   return Scheme(P,[Evaluate(g,equ) : g in bas]);
end function;

// Balance
// INPUT: two sequences n,d of the same length
// OUTPUT: a sequence a such that that SV_a^n and SV_{d-a}^n are ''balanced''

Balance := function(n,d)
 a := [0:j in [1..#n]];
 b := [0:j in [1..#n]];
 a[1] := Floor(d[1]/2);
 b[1] := d[1]-a[1];
 for j in [2..#n] do
  if &*[Binomial(a[i]+n[i],n[i]) : i in [1..j-1]] ge &*[Binomial(b[i]+n[i],n[i]) : i in [1..j-1]] then
   a[j] := Floor(d[j]/2);
  else
   a[j] := Ceiling(d[j]/2);
  end if;
  b[j] := d[j]-a[j];
 end for;
 return a;
end function;

// Flattening
// INPUT: three sequences n,d,k of the same length, a field Q
// OUTPUT: a matrix M and three lists of monomials mon2,mon1,mon for 
// the flattening P^{#mon1-1}->P^{#mon2-1} of the Segre-Veronese tensor
// decomposed according to the (k,d-k) splitting

Flattening := function(n,d,k,Q)
 r := &+n+#n;
 s := &*[Binomial(n[i]+d[i],d[i]) : i in [1..#n]];
 K<[T]> := FunctionField(Q,s);
 R<[x]> := PolynomialRing(K,r);
 lis := [];
 lis1 := [];
 lis2 := [];
 for i in [1..#n] do
  B := Basis(ToricLattice(n[i]+1));
  Append(~lis,Polytope([d[i]*b : b in B]));
  Append(~lis1,Polytope([k[i]*b : b in B]));
  Append(~lis2,Polytope([(d[i]-k[i])*b : b in B]));
 end for;
 pts := [&cat[Eltseq(m[i]) : i in [1..#n]] : m in CartesianProduct(<Points(P) : P in lis>)];
 pts1 := [&cat[Eltseq(m[i]) : i in [1..#n]] : m in CartesianProduct(<Points(P) : P in lis1>)];
 pts2 := [&cat[Eltseq(m[i]) : i in [1..#n]] : m in CartesianProduct(<Points(P) : P in lis2>)];
 mon := Reverse(Sort([Monomial(R,Eltseq(p)) : p in pts]));
 mon1 := Reverse(Sort([Monomial(R,Eltseq(p)) : p in pts1]));
 mon2 := Reverse(Sort([Monomial(R,Eltseq(p)) : p in pts2]));
 tensor := &+[T[i]*mon[i] : i in [1..#mon]];
 M := Matrix([[MonomialCoefficient(Hder(tensor,Exponents(m)),p) : p in mon2] : m in mon1]);
 return M,mon2,mon1,mon;
end function;

// Identify
// INPUT: three sequences n,d,k of the same length m, 
// a sequence v with the coefficients of the tensor T,
// a positive integer h (the tensor rank), a field Q
// OUTPUT: it has 5 outputs: 
// 1) the subscheme of P^n_1 x ... x P^n_m of the h points
// representing the linear forms which identify T;
// 2) a linear space;
// 3) two lists of monomials mon2,mon1 and a matrix M for 
// the flattening P^{#mon1-1}->P^{#mon2-1} of the Segre-Veronese tensor T
// decomposed according to the (k,d-k) splitting

Identify := function(n,d,k,v,h,Q)
 M,mon2,mon1,mon := Flattening(n,d,k,Q);
 r := Rank(Parent(mon2[1]));
 nr := Nrows(M);
 nc := Ncols(M);
 Matflat := Matrix(nr,nc,[Evaluate(Numerator(p),v) : p in Eltseq(M)]);
 K := Image(Matflat);
 L := ToricLattice(#n);
 b := Eltseq(L!d-L!k);
 Matsec := Flattening(n,b,Balance(n,b),Q);
 u := Max(h-&*[Binomial(k[i]+n[i],n[i]) : i in [1..#n]]+1,1);
 ll := Minors(Matsec,u+1);
 PP := Proj(Parent(Numerator(ll[1])));
 X := Scheme(PP,ll);
 H := Span({PP!Eltseq(p) : p in Basis(K)});
 return X meet H,H,mon2,mon1,Matflat;
end function;


// IdentifyParam
// INPUT: three sequences n,d,k of the same length m, 
// a sequence v with the coefficients of the tensor T,
// a positive integer h (the tensor rank), a field Q
// OUTPUT: it has 2 outputs: 
// 1) the subscheme of A^n_1 x ... x A^n_m x A^(h-1) 
// corresponding to the h-points representing the linear forms 
// which identify T;
// 2) a general point in the image of the parametrization

IdentifyParam := function(n,d,v,k,h,Q)
 A<[z]> := &*[&*[AffineSpace(Q,u) : u in n] : i in [1..h]]*AffineSpace(Q,h-1);
 M,mon2,mon1,mon := Flattening(n,d,k,Q);
 r := Rank(Parent(mon2[1]));
 nr := Nrows(M);
 nc := Ncols(M);
 Matflat := Matrix(nr,nc,[Evaluate(Numerator(p),v) : p in Eltseq(M)]);
 K := Kernel(Transpose(Matflat));
 lis := [];
 for i in [1..h] do
  u := [];
  for j in [1..#n] do
   s := &+n[1..j]-n[j]+(i-1)*&+n;
   u := u cat z[1+s..n[j]+s] cat [1];
  end for;
  Append(~lis,Vector([Evaluate(m,u) : m in mon2]));
 end for;
 ve := [Exponents(m) : m in mon2];
 cf := [Factorial(&+u)/&*[Factorial(u[j]) : j in [1..#u]] : u in ve];
 if h eq 1
  then w := lis[1];
  else
   w := &+[z[&+n*h+i-1]*(lis[i]-lis[1]) : i in [2..#lis]]+lis[1];
 end if;
 equ := [&+[cf[i]*w[i]*Eltseq(p)[i] : i in [1..#mon2]] : p in Basis(K)];
 return Scheme(A,equ),w;
end function;


// IsIdentifiable
// INPUT: three sequences n,d,k of the same length m, 
// a sequence v with the coefficients of the tensor T,
// a positive integer h (the tensor rank), a field Q
// OUTPUT: boolean 

IsIdentifiable := function(n,d,k,v,h,Q)
 a := Min(&*[Binomial(k[i]+n[i],n[i]) : i in [1..#n]]-1,h-1);
 Z := Identify(n,d,k,v,h,Q);
 if Dimension(Z) eq 0 and Degree(Z) eq Binomial(h,a) then return true; end if;
 return false;
end function;


// IdentifyForms
// INPUT: three sequences n,d,k of the same length m,
// a sequence v with the coefficients of the tensor T,
// a positive integer h (the tensor rank), a field Q
// OUTPUT: the linear forms which identify T obtained by the flattening given by k

IdentifyForms := function(n,d,k,v,h,Q)
 Abar := Min(&*[Binomial(k[i]+n[i],n[i]) : i in [1..#n]]-1,h-1);
 r := Binomial(h-1,Abar-1);
 Z, H, mon2, mon1, Matflat := Identify(n,d,k,v,h,Q);
 Pn<[y]> := ProjectiveSpace(Q,#mon1-1);
 PN := ProjectiveSpace(Q,#mon2-1);
 pi := map<Pn->PN|[&+[Pn.j*Matflat[j,i] : j in [1..#mon1]] : i in [1..#mon2]]>;
 W := Scheme(Pn,[Evaluate(b,DefiningEquations(pi)) : b in Basis(Ideal(Z))]);
 pp := Points(W);
 forms := {};
 repeat
  pts := [];
  repeat
   Include(~pts,Random(pp));
  until #pts eq Dimension(Pn);
   lis := [q : q in pp | Rank(Matrix([Eltseq(p) : p in pts] cat [Eltseq(q)])) eq Dimension(Pn)];
  if #lis eq r then 
   M := Matrix([Eltseq(p) : p in pts]);
   w := Eltseq(Basis(Kernel(Transpose(M)))[1]);
   forms := forms join {&+[Pn.i*w[i] : i in [1..#w]]};
  end if;
 until #forms eq h;
 if #n eq 1 and k[1] gt 1 then
  r := &+n+#n;
  P<[z]> := ProjectiveSpace(Q,r-1);
  u:=1;
  for j in [1..#n] do
   s := &+n[1..j]-n[j]+j-1;
   u := u*((&+z[1+s..n[j]+1+s])^k[j]);
  end for;
  ver := map<P->Pn|[mon1[j]*MonomialCoefficient(u,Exponents(mon1[j])):j in [1..#mon1]]>;
 forms2 := [Evaluate(g,DefiningEquations(ver)) : g in forms];
 forms := [Factorization(g)[1][1]: g in forms2];
 end if;
 return [p: p in forms];
end function;


// IdentifyTensor
// INPUT: two sequences n,d of the same length m, 
// a sequence v with the coefficients of the tensor T,
// a positive integer h (the tensor rank), a field Q
// This function covers the cases of Veronese, d=[1,2], d=[2,1] and d=[1,1,1].
// OUTPUT: the linear forms which identify T.
// If (n,d,v,h,Q) is not identifiable then it returns false,[]
// If the case (n,d,v,h,Q) is not covered by algorithm it returns [],[]

IdentifyTensor := function(n,d,v,h,Q)
 M,mon2,mon1,mon := Flattening(n,d,[1] cat [0: j in [2..#n]],Q);
 r := &+n+#n;
 R<[x]> := PolynomialRing(Q,r);
 f := &+[R!mon[j]*v[j]: j in [1..#mon]];
 if #n eq 1 then 
  if not IsIdentifiable(n,d,[Floor(d[1]/2)],v,h,Q) then
   return false,[];
  end if;
  Forms:= [Evaluate(p,[x[j]: j in [1..n[1]+1]]) : p in IdentifyForms(n,d,[Floor(d[1]/2)],v,h,Q)];
  L := LinRelPols([-f] cat [Forms[k]^d[1]: k in [1..h]]);
  return [[Forms[k]]: k in [1..h]], Eltseq(L[1])[2..#Eltseq(L[1])];
 end if;
 if d eq [2,1] or d eq [1,2] then
  if not IsIdentifiable(n,d,[1,0],v,h,Q) or not IsIdentifiable(n,d,[0,1],v,h,Q) then
   return false,[];
  end if;
  FirstForms := [Evaluate(p,[x[j]: j in [1..n[1]+1]]) : p in IdentifyForms(n,d,[1,0],v,h,Q)];
  SecondForms := [Evaluate(p,[x[j]: j in [n[1]+2..n[1]+n[2]+2]]) : p in IdentifyForms(n,d,[0,1],v,h,Q)];
  seqs := SequencesofGivenSize(h);
  for seq1 in seqs do
   L := LinRelPols([-f] cat [FirstForms[k]^d[1]*SecondForms[seq1[k]]^d[2]: k in [1..h]]);
   if #L ne 0 then
    return [[FirstForms[k],SecondForms[seq1[k]]]: k in [1..h]], Eltseq(L[1])[2..#Eltseq(L[1])];;
   end if;
  end for;
 end if;
 if d eq [1,1,1] then
  if not IsIdentifiable(n,d,[1,0,0],v,h,Q) or not IsIdentifiable(n,d,[0,1,0],v,h,Q) or not 
IsIdentifiable(n,d,[0,1,0],v,h,Q) then
   return false,[];
  end if;
  FirstForms := [Evaluate(p,[x[j]: j in [1..n[1]+1]]) : p in IdentifyForms(n,d,[1,0,0],v,h,Q)];
  SecondForms := [Evaluate(p,[x[j]: j in [n[1]+2..n[1]+n[2]+2]]) : p in IdentifyForms(n,d,[0,1,0],v,h,Q)];
  ThirdForms := [Evaluate(p,[x[j]: j in [n[1]+n[2]+3..r]]) : p in IdentifyForms(n,d,[0,0,1],v,h,Q)];
  seqs := SequencesofGivenSize(h);
  for seq1,seq2 in seqs do
   L := LinRelPols([-f] cat [FirstForms[k]^d[1]*SecondForms[seq1[k]]^d[2]*ThirdForms[seq2[k]]^d[3]: k in [1..h]]);
   if #L ne 0 then
    return [[FirstForms[k],SecondForms[seq1[k]],ThirdForms[seq2[k]]]: k in [1..h]], Eltseq(L[1])[2..#Eltseq(L[1])];
   end if;
  end for;
 end if;
 return false,false;
end function;

// TensorOfRank
// INPUT: two sequences n,d of the same length, 
// a positive integer h (the tensor rank), a field Q
// OUTPUT: a sequence with the coefficients of a random tensor of rank h,
// the corresponding linear forms, the coefficients, the tensor.

TensorOfRank := function(n,d,h,Q)
 r := &+n+#n;
 s := &*[Binomial(n[i]+d[i],d[i]) : i in [1..#n]];
 R<[x]> := PolynomialRing(Q,r);
 V := VectorSpace(Q,s);
 lis := [];
 for i in [1..#n] do
  B := Basis(ToricLattice(n[i]+1));
  Append(~lis,Polytope([d[i]*b : b in B]));
 end for;
 ll := [];
 for k in [1..h] do
  lin := [];
  c := 0;
  for i in [1..#n] do
   Append(~lin,&+[Rnd(Q)*x[j] : j in [c+1..c+n[i]+1]]);
   c := c + n[i] + 1;
  end for;
  Append(~ll,lin);
 end for;
 coef:= [Rnd(Q): j in [1..h]];
 f := &+[coef[j]*&*[ll[j][i]^d[i]: i in [1..#n]]: j in [1..h]];
 pts := [&cat[Eltseq(m[i]) : i in [1..#n]] : m in CartesianProduct(<Points(P) : P in lis>)];
 mon := Reverse(Sort([Monomial(R,Eltseq(p)) : p in pts]));
 return [MonomialCoefficient(f,m) : m in mon],ll,coef,f;
end function;


// TensorFromPol
// INPUT: two sequences n,d of the same length, a polynomial F
// OUTPUT: a sequence with the coefficients of the tensor F

TensorFromPol := function(n,d,F)
 Q := BaseRing(Parent(F));
 r := &+n+#n;
 s := &*[Binomial(n[i]+d[i],d[i]) : i in [1..#n]];
 R<[x]> := PolynomialRing(Q,r);
 F := R!F;
 V := VectorSpace(Q,s);
 lis := [];
 for i in [1..#n] do
  B := Basis(ToricLattice(n[i]+1));
  Append(~lis,Polytope([d[i]*b : b in B]));
 end for;
 pts := [&cat[Eltseq(m[i]) : i in [1..#n]] : m in CartesianProduct(<Points(P) : P in lis>)];
 mon := Reverse(Sort([Monomial(R,Eltseq(p)) : p in pts]));
 return [MonomialCoefficient(F,m) : m in mon];
end function;


// IsSexticGeneric
// INPUT: a plane sextic F
// OUTPUT: true if F has rank 9 and false otherwise

IsSexticGeneric := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 mon3 := MonomialsOfDegree(R,3);
 P9 := ProjectiveSpace(Q,9);
 H9:=Span({P9![MonomialCoefficient(l,p): p in mon3] : l in
 [R!Hder(F,Exponents(p)): p in mon3]});
 return Dimension(H9) eq 8;
end function;


// IsQuinticGeneric
// INPUT: a plane quintic F
// OUTPUT: true if F has rank 7 and false otherwise

IsQuinticGeneric := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 mon2 := MonomialsOfDegree(R,2);
 mon3 := MonomialsOfDegree(R,3);
 P9 := ProjectiveSpace(Q,9);
 H9:=Span({P9![MonomialCoefficient(l,p): p in mon3] : l in
 [R!Hder(F,Exponents(p)): p in mon2]});
 return Dimension(H9) eq 5;
end function;


// PolynomialOfRank
// INPUT: three positive integers n,d and h (the tensor rank), a field Q
// OUTPUT: a random polynomial c_1*L_1^d+...+c_h* L_h^d of degree d and 
// rank h with n+1 variables over Q,
// the list of linear forms L_1,..,L_h,
// the list of coefficients c_1,...,c_h.

PolynomialOfRank := function(n,d,h,Q)
 a,ll,coef := TensorOfRank([n],[d],h,Q);
 F := &+[coef[j]*ll[j][1]^d : j in [1..h]];
 if n eq 2 and d eq 6 and h eq 9 then
  while not IsSexticGeneric(F) do
   a,ll,coef := TensorOfRank([n],[d],h,Q);
   F := &+[coef[j]*ll[j][1]^d : j in [1..h]];
  end while;
 end if;
 if n eq 2 and d eq 5 and h eq 7 then
  while not IsQuinticGeneric(F) do
   a,ll,coef := TensorOfRank([n],[d],h,Q);
   F := &+[coef[j]*ll[j][1]^d : j in [1..h]];
  end while;
 end if;
 return F,[p[1]: p in ll],coef;
end function;


// Hilbert
// INPUT: a plane quintic rank 7 and a field Q
// OUTPUT: the components of the quintic

Hilbert := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 P2 := Proj(R);
 R2 := CoordinateRing(P2);
 P3 := ProjectiveSpace(Q,3);
 P9 := ProjectiveSpace(Q,9);
 A3<[w]> := AffineSpace(Q,3);
 R9 := CoordinateRing(P9);
 mon2 := MonomialsOfDegree(R,2);
 mon3 := MonomialsOfDegree(R,3);
 H:=Span({P9![MonomialCoefficient(l,p): p in mon3] : l in
 [R!Hder(F,Exponents(p)): p in mon2]});
 f := map<P2->P9 | Terms((P2.1+P2.2+P2.3)^3)>;
 g := map<P9->P3 | MinimalBasis(H)>;
 h := map<P2->P3 | DefiningEquations(f*g)>;
 V := Image(f);
 // Here we going to use that the image of h in P3 is a hypersurface of degree 9
 mon := MonomialsOfDegree(CoordinateRing(P3),9);
 lr := Eltseq(LinRelPols([Evaluate(m,DefiningEquations(h)) : m in mon])[1]);
 G := &+[lr[i]*mon[i] : i in [1..#mon]];
 DG := [Evaluate(Derivative(G,6,i),w cat [1]) : i in [1..3]];
 R3 := CoordinateRing(A3);
 J := ideal<R3 | DG cat [Evaluate(G,w cat [1])]>;
 X := Scheme(A3,J);
 while Dimension(X) ne 0  do
  d1:=Random([1..4]);
  d2:=Random([1..5-d1]);
  Append(~DG,Evaluate(Derivative(Derivative(Derivative(G,d1,1),d2,2),6-d1-d2),w cat [1]));
  J := ideal<R3 | DG cat [Evaluate(G,w cat [1])]>;
  X := Scheme(A3,J);
 end while;
 while #Points(X) ne 1  do
  d1:=Random([1..4]);
  d2:=Random([1..5-d1]);
  Append(~DG,Evaluate(Derivative(Derivative(Derivative(G,d1,1),d2,2),6-d1-d2),w cat [1]));
  J := ideal<R3 | DG cat [Evaluate(G,w cat [1])]>;
  X := Scheme(A3,J);
 end while;
 p := Points(X)[1];
 fib := Fiber(g,Cluster(P3,P3!(Eltseq(p) cat [1])));
 if Characteristic(Q) eq 0 then
  pts := Points(Fiber(f,fib meet V));
 else 
  pts := PointsOverSplittingField(Fiber(f,fib meet V));
 end if;
 lis := Sort([&+[P2.i*p[i] : i in [1..3]] : p in pts]);
 ll := Eltseq(LinRelPols([F] cat [f^5 : f in lis])[1]);
 return lis,[-ll[c] : c in [2..#ll]];
end function;



// DecomposeSextic
// INPUT: a plane sextic of rank 9 and a field Q
// OUTPUT: the two decompositions of the sextic

DecomposeSextic := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 P2 := Proj(R);
 mon2 := MonomialsOfDegree(R,2);
 mon3 := MonomialsOfDegree(R,3);
 mon4 := MonomialsOfDegree(R,4);
 P9 := ProjectiveSpace(Q,9);
 g := map<P2->P9 | [p*MonomialCoefficient((&+[P2.j: j in [1..3]])^3,p): p in mon3]>;
 H9:=Span({P9![MonomialCoefficient(l,p): p in mon3] : l in
 [R!Hder(F,Exponents(p)): p in mon3]});
 C9 := g(P2) meet H9;
 P14 := ProjectiveSpace(Q,14);
 P8 := ProjectiveSpace(Q,8);
 C2 := Fiber(g,C9);
 H14:=Span({P14![MonomialCoefficient(l,p): p in mon4] : l in
 [R!Hder(F,Exponents(p)): p in mon2]});
 f := map<P2->P14 | [p*MonomialCoefficient((&+[P2.j: j in [1..3]])^4,p): p in mon4]>;
 pi:= map<P14->P8 | MinimalBasis(H14)>;
 fpi := map<P2->P8 | DefiningEquations(f*pi)>;
 C8 := fpi(C2);
 Min8 := Basis(Ideal(C8));
 U:=Scheme(P8,[p:p in Min8|Degree(p) eq 1]);
 P5 := ProjectiveSpace(Q,5);
 Rw:=CoordinateRing(P5);
 MinU:=MinimalBasis(U);
 K:=Transpose(Matrix(Basis(Kernel(Transpose(Matrix([[Derivative(MinU[j],i): i in [1..9]]:j in  [1..#MinU]]))))));
 h:=map<P5->P8|[&+[P5.j*(Rw!k[j]): j in [1..6]]:k in Rows(K)]>;
 eqh:=DefiningEquations(h);
 X:=Scheme(P5,[Evaluate(g,eqh) : g in Min8 | Degree(g) eq 2]);
 Z := {};
 repeat
  repeat
   ll := [&+[Random(Rationals(),100)*P5.i : i in [1..6]] : j in [1,2]];
   pts := Points(Scheme(X,ll));
  until #pts gt 0;
  for p in pts do
   L := TangentSpace(X,p) meet X;
   if Dimension(L) eq 2 then Include(~Z,L); end if;
  end for;
 until #Z eq 2;
// cc := PrimeComponents(SingularSubscheme(X));
// Z := [Span(P5,C) : C in cc];
// Z:=PrimeComponents(X);
 C5:=Scheme(P5,[Evaluate(g,eqh) : g in Min8 | Evaluate(g,eqh) ne 0]);
// decomp5:=[z meet C5: z in Z| Degree(z) eq 1 and Dimension(z) eq 2];
 decomp5:=[z meet C5: z in Z];
 return [Fiber(f*pi,h(z)): z in decomp5];
end function;


// Sextic
// INPUT: a plane sextic of rank 9 and a field Q
// OUTPUT: the components of one decomposition of the sextic

Sextic := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 P2 := Proj(R);
 decomp2 := DecomposeSextic(F);
 pts := Sort([[[p[j]:j in [1..3]]:p in Points(decomp2[j])]: j in [1..#decomp2] | #Points(decomp2[j]) eq 9][1]);
 lis := Sort([&+[P2.i*p[i] : i in [1..3]] : p in pts]);
 ll := Eltseq(LinRelPols([F] cat [f^6 : f in lis])[1]);
 return lis,[-ll[c] : c in [2..#ll]];
end function;


// Septic
// INPUT: a plane septic of rank 12 and a field Q
// OUTPUT: the components of the septic

Septic := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 P2 := Proj(R);
 P14 := ProjectiveSpace(Q,14);
 P4 := ProjectiveSpace(Q,4);
 mon3 := MonomialsOfDegree(R,3);
 H:=Span({P14![MonomialCoefficient(l,p): p in Monomials((&+[P2.j: j in [1..3]])^4)] : l in [R!Hder (F,Exponents(p)): p 
in mon3]});
 f := map<P2->P14 | Terms((&+[P2.j: j in [1..3]])^4)>;
 pi := map<P14->P4 | MinimalBasis(H)>;
 fpi := map<P2->P4 | DefiningEquations(f*pi)>;
 VP:= fpi(P2);
 W:=Scheme(P4,[p: p in Basis(Ideal(VP))| Degree(p) le 11]);
 X := Scheme(P4,Saturation(Ideal(W),Ideal(VP)));
 L := IrreducibleComponents(X);
 for j in [1..#L] do
  Z:=Fiber(fpi,L[j]);
  auxpts := Points(Z);
  if #auxpts eq 12 then 
   pts:=auxpts;
  end if;
 end for;
 lis := Sort([&+[P2.i*p[i] : i in [1..3]] : p in pts]);
 ll := Eltseq(LinRelPols([F] cat [f^7 : f in lis])[1]);
 return lis,[-ll[c] : c in [2..#ll]];
end function;

// Nonic
// INPUT: a plane nonic of rank 17 and a field Q
// OUTPUT: the components of the nonic

Nonic := function(F)
 R := Parent(F);
 Q := BaseRing(R);
 P2 := Proj(R);
 P20 := ProjectiveSpace(Q,20);
 P5 := ProjectiveSpace(Q,5);
 mon4 := MonomialsOfDegree(R,4);
 H:=Span({P20![MonomialCoefficient(l,p): p in Monomials((&+[P2.j: j in [1..3]])^5)] : l in [R!Hder (F,Exponents(p)): p in mon4]});
 f := map<P2->P20 | Terms((&+[P2.j: j in [1..3]])^5)>;
 pi := map<P20->P5 | MinimalBasis(H)>;
 fpi := map<P2->P5 | DefiningEquations(f*pi)>;
 VP:= fpi(P2);
 W := Scheme(P5,[p: p in Basis(Ideal(VP))| Degree(p) le 16]);
 X := Scheme(P5,Saturation(Ideal(W),Ideal(VP)));
 L := IrreducibleComponents(X);
 for j in [1..#L] do
  Z:=Fiber(fpi,L[j]);
  auxpts := Points(Z);
  if #auxpts eq 17 then
   pts:=auxpts;
  end if;
 end for;
 lis := Sort([&+[P2.i*p[i] : i in [1..3]] : p in pts]);
 ll := Eltseq(LinRelPols([F] cat [f^9 : f in lis])[1]);
 return lis,[-ll[c] : c in [2..#ll]];
end function;
