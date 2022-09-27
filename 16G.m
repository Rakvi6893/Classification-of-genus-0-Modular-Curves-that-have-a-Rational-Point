/* For the genus 0 congruence subgroup with Cummins Pauli label 16G0, when we compute a pair (P^1,\pi) with properties as explained in 
section 8.1 we notice that there are some nontrivial cocycles from Gal(K/Q) -> A_{G_1}. For each such cocycle we compute the set of cocycles
{Gamma_j'} as explained in paragraph following lemma 8.5 at level 15. For each Gamma_j' we compute the twist corresponding to it along with j-map. */


function EvaluateRationalFunction(f,a)
/* Input: f a rational function in some K(t), a is an element of K o\
r a pair giving a point in P^1(K). The function returns f(a) as a pair represe\
nting a point in P^1(K); it is [1,0] or of the form [x,1]. */
if Type(a) ne SeqEnum then
     a:=[a,1];
 end if;
 num:=Numerator(f);
den:=Denominator(f);
 d1:=Degree(num);
 d2:=Degree(den);
 if a[2] eq 0 and d1 gt d2 then
    return [1,0];
 end if;
if a[2] eq 0 and d1 lt d2 then
     return [0,1];
 end if;
if a[2] eq 0 and d1 eq d2 then
   return [Coefficient(num,d1)/Coefficient(den,d2),1];
 end if;
 a:=a[1]/a[2];
 if Evaluate(den,a) eq 0 then
     return [1,0];
 end if;
 return [Evaluate(num,a)/Evaluate(den,a), 1];
 end function;

 function ValuationRationalFunction(f,P)
 /* Give a non-zero rational function f in K(t) returns the valuation\
 at the point P. */
 K:=BaseRing(Parent(f));
if Type(P) ne SeqEnum then
    return ValuationRationalFunction(f,[P,1]);
 end if;
 if P[2] eq 0 then
     return Degree(Denominator(f))-Degree(Numerator(f));
 end if;
 a:=K!(P[1]/P[2]);
 Pol<t>:=PolynomialRing(K);
 n:=Pol!Numerator(f);
d:=Pol!Denominator(f);
 return Valuation(n,t-a)-Valuation(d,t-a);
 end function;

function RationalMap0(a,b,c,K)
 /*  Given three distinct elements a,b,c in P^1(K) gives the unique d\
egree 1 rational function in K(t) such that the induced map P^1 -> P^1 takes a to 0, b to \
1 and c to infinity. We can take a,b,c to be a non-zero pair in K^2 or a number d in \
K meaning [d,1]. The point at infinity is [1,0]. */
     if Type(a) ne SeqEnum then a:=[a,1]; end if;
     if Type(b) ne SeqEnum then b:=[b,1]; end if;
     if Type(c) ne SeqEnum then c:=[c,1]; end if;
     F<t>:=FunctionField(K);
    if c[2] eq 0  then a:=a[1]/a[2]; b:=b[1]/b[2];  return (t-a)/(b-a); end if;
    if b[2] eq 0  then a:=a[1]/a[2]; c:=c[1]/c[2];  return (t-a)/(t-c); end if;
     if a[2] eq 0  then b:=b[1]/b[2]; c:=c[1]/c[2];  return (b-c)/(t-c); end if;
    a:=a[1]/a[2]; b:=b[1]/b[2]; c:=c[1]/c[2];       return (t-a)/(t-c)*(b-c)/(b-a);
 end function;

function RationalInverse(f)
 /*  For a rational function f in K(t) of degree 1 computes g in K(t)\
 so that g(f(t))=t=f(g(t)).*/
    K:=BaseRing(Parent(f));
     F<t>:=FunctionField(K); f:=F!f;
   b:= Evaluate(Numerator(f),0);    a:= Evaluate(Numerator(f)-b,1);
    d:= Evaluate(Denominator(f),0);  c:= Evaluate(Denominator(f)-d,1);
     return (d*t-b)/(-c*t+a);
 end function;

 function RationalMap(a,b,c,aa,bb,cc,K)
 /* Input: Distinct a,b,c in P^1(K) and distinct aa,bb,cc in P^1(K) w\
ith K a field. Output: The unique rational function in K(t) that induces an is\
omorphism P^1 -> P^1 which takes a,b,c to aa,bb,cc, respectively. */
 F:=FunctionField(K);
 f1:=RationalMap0(a,b,c,K);
 f2:=RationalMap0(aa,bb,cc,K);
 return Evaluate(RationalInverse(f2),f1);
 end function;

function SameRationalParametrization(J1,J2,K : findall:=true, triple:=[ [r[1],1] : r in Roots(Denominator(J1))] cat [ [2,1] ]);
 /* Input: J1, J2 non-constant elements of K(t) Output: Returns true \
if J1(t) = J2(f(t)) for some f in K(t) of degree 1; otherwise false. If true, \
the also outputs f (returns the set of all possible f if "findall" is true). N\
ote: f is searched for by solving J1(a)=J2(f(t)) for three different a in P^1(\
K); the three values used can be set by changing "triple". */
 F:=FunctionField(K);
 J1:=F!J1;
 J2:=F!J2;
 if #triple ge 3 then
     triple:=[triple[i]: i in [1..3]];
 else
     triple:=[[1,0],[0,1],[1,1]];
 end if;
 RR:=[];
 for i in [1..3] do
    P:=triple[i];
    if Type(P) ne SeqEnum then
        P:=[P,1];
    end if;
    v:=ValuationRationalFunction(J1,P);
     Q:=EvaluateRationalFunction(J1,P);
    if Q[2] ne 0 then
        num:=Numerator(J2-Q[1]/Q[2]);
        den:=Denominator(J2-Q[1]/Q[2]);
    else
        num:=Numerator(J2);
        den:=Denominator(J2);
     end if;
  R:=[[r[1],1]: r in Roots(num) cat Roots(den)] cat [[1,0]];
   R:=[r: r in R | ValuationRationalFunction(J2,r) eq v];
    if #R eq 0 then
        return false;
    end if;
   RR:=RR cat [R];
end for;
 F:={};
 for a in RR[1], b in RR[2], c in RR[3] do
    if #{a,b,c} eq 3 then
         f:=RationalMap(triple[1],triple[2],triple[3], a,b,c,K);
        if Evaluate(J2,f) eq J1 then
            F:=F join {f};
                if findall eq false then
                    return true,
                   f;
                 end if;
        end if;
    end if;
 end for;
 if #F eq 0 then
    return false;
 end if;
 return true, F;
end function;

 function H90(n,L,K,G,sigma,xi)
 // Input: xi: G=Gal(L/K)-> GL(n,L) 1-cocycle.
 // Output: matrix A in GL(n,L) such that xi_g = A^(-1) g(A) for all g in G.

    V := VectorSpace(L,n);
     B1:=Basis(L);  // Warning: assuming K is base field of L
     B2:=Basis(V);
     B:=[b*v: b in B1, v in B2];

   S:={};

     i:=1;

     while Dimension(sub<V|S>) ne n do

       v:=B[i];
       tr:=&+[ xi(g)*Matrix(L,n,1,[sigma(g)(v[i]): i in [1..n]]) : g in G] / #G;        
       tr:=V!Transpose(tr);

        if Dimension(sub<V|S join {tr}>) gt Dimension(sub<V|S>) then
           S:=S join {tr};
        end if;
        i:=i+1;
    end while;
    A0:=Transpose(Matrix([ ElementToSequence(v) : v in S ]));
    
    A:=A0^(-1);
   // Check:
    for g in G do
       gA:=Matrix([ [sigma(g)(A[i,j]):j in [1..n]] : i in [1..n]]);
        assert A^(-1)*gA eq xi(g);
    end for;
    return A;
 end function;
 function m2(A,K)
// Input : A matrix A in GL_{3}(K) such that A preserves the equation for y^2=xz
// Output : A matrix C in GL_{2}(K) corresponding to A
a := A[1,1];
 b := A[1,2];
 c := A[1,3];
d := A[2,1];
e := A[2,2];
 f := A[2,3];
 g := A[3,1];
 h := A[3,2];
i := A[3,3];
if a eq 0 then
    C := Matrix(K,2,2,[0,c,e,f]);
else
    if g eq 0 then
        C := Matrix(K,2,2,[a,b/2,0,e]);
    else
        if c eq 0 then
             C := Matrix(K,2,2,[a,0,d,e]);
        else
             if f eq 0 then
                C := Matrix(K,2,2,[a,b/2,d,0]);
            else
                C := Matrix(K,2,2,[a,b/2,d,e-(b*d/(2*a))]);
            end if;
        end if;
    end if;
end if;
return C;
end function;

function psi(g,N,M,b)

/* Input : 1) Here M,N and b are integers such that M is coprime to N and every prime factor of b is also a prime factor of N.
           2) Here g is an element of Gal(K_{M*N*b}/K_M).
	   
   Output :Returns an element g1 of Gal(K_{N*b}/Q) that respects the action of g on primitive N*b-th root of unity. */ 
	   

L<z1>:= CyclotomicField(M*N*b);
L1<z>:=CyclotomicField(N*b);
z:=L!z;
G1,_,sigma1:=AutomorphismGroup(L1);
G2,_,sigma2:=AutomorphismGroup(L,CyclotomicField(M));
g := G2!g;
for g1 in G1 do;
    if sigma1(g1)(z) eq sigma2(g)(z) then return g1; break;end if;
end for;
end function;



SetOutputFile("16Gdata.m": Overwrite := true);

N:=16;
b:=2;
M:=15;
L<z1>:= CyclotomicField(M*N*b);
L1<z>:=CyclotomicField(N*b);
z:=L!z;
G1,_,sigma1:=AutomorphismGroup(L1);
G2,_,sigma2:=AutomorphismGroup(L,CyclotomicField(M));
psi:=map<G2->G1|[g->psi(g,N,M,b): g in G2]>;

S<t> := FunctionField(L);

    
   JG:=(256*t^48 + 768*t^40 + 1536*t^32 + 1792*t^24 + 1536*t^16 + 768*t^8 + 256)/(t^32 + 2*t^24 + t^16); 
    _,AG:=SameRationalParametrization(JG,JG,L);
    m1 := map< MatrixRing(L,2) -> MatrixRing(L,3) | n :-> (1/Determinant(n))*Matrix(3,3,[n[1,1]^2,2*n[1,1]*n[1,2],n[1,2]^2,n[1,1]*n[2,1],n[1,1]*n[2,2]+n[1,2]*n[2,1],n[1,2]*n[2,2],n[2,1]^2,2*n[2,1]*n[2,2],n[2,2]^2])>;
    G,iota,sigma:=AutomorphismGroup(L); 
    R :={}; 
    for f in AG do; 
        R := R join {[Evaluate(Numerator(f)-Evaluate(Numerator(f),0),1),Evaluate(Numerator(f),0),Evaluate(Denominator(f)-Evaluate(Denominator(f),0),1),Evaluate(Denominator(f),0)]}; 
    end for; 

    R := sub<GL(3,L)|[m1(r): r in R]>;  
    action := hom<G -> Aut(R)|g :-> iso<R->R | n :-> [[(sigma(g))(n[i,j]): j in [1..Ncols(n)]]: i in [1..Nrows(n)]]>>; 
   
    A := GammaGroup(G,R,action); 
   
    
    H1 := OneCohomologyFP(A);
    
    zeta1 := map<G1 -> MatrixRing(L,2) |[Id(G1)->
[1 ,0, 0,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1 , -1, 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[   1 ,   0, 0, 1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[1,0,0,1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[0,1,-1,0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[ 0,1,-1,0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[1  ,0,  0,1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[1  ,0 , 0, 1 ],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, 1,-1,0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0,  1, -1,0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[    1 ,   0 ,  0,  1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[ 1,0,0,1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[  0,     1  ,   -1,   0 ],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[0 , 1, -1,  0 ],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1 ,0, 0 ,1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,  -1, 0]]>;
zeta1:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta1(g)):g in G1]>;
zeta11:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0,  1,-1,  0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[-1,  0,0,  1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[-1,  0,0 , 1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[ 0, -1,-1,  0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[ 0, -1,-1,  0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[1, 0,0 ,1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[1 ,0,0 ,1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0 , 1,-1 , 0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0  ,1,-1 , 0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[-1 , 0,0,  1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[-1 , 0,0 , 1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[ 0, -1,-1 , 0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[ 0 ,-1,-1 , 0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1, 0,0, 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0,  1,-1,  0]]>;
zeta11:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta11(g)):g in G1]>;
zeta2 := map<G1 -> MatrixRing(L,2) |[Id(G1)->
[1 ,0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1,  0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[    0, -z^12, -1 ,    0],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[   0 ,z^12, -1 ,   0],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[-z^12 ,    0,0 ,    1],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[z^12 ,   0, 0 ,   1],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0,0 , 1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1 , 0,0 , 1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, -1,-1,  0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0 ,-1,-1 , 0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[   0 ,z^12,-1 ,   0],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[    0, -z^12,  -1 ,    0],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[z^12 ,   0, 0 ,   1],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[-z^12  ,   0,   0 ,    1],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1, 0,0, 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,-1  ,0]]>;
zeta2:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta2(g)):g in G1]>;
zeta21:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1 ,0,0, 1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1,  0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[   0 ,z^12,-1 ,   0],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[    0, -z^12, -1 ,    0],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[z^12  ,  0, 0 ,   1],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[-z^12 ,    0, 0 ,    1],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0,0,  1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1  ,0,0,  1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, -1,-1,  0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0 ,-1,-1,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[    0, -z^12, -1,     0],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[   0, z^12,-1,    0],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[-z^12 ,    0, 0 ,    1],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[z^12 ,   0, 0 ,   1],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1 ,0,0, 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,-1,  0]]>;
zeta21:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta21(g)):g in G1]>;
zeta22:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0, 1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0,  1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[   0, -z^4, -1 ,   0],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[  0 ,z^4, -1,   0],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[-z^4   , 0,0   , 1],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[z^4 ,  0,0  , 1],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0,0 , 1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1  ,0,0 , 1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, -1,-1,  0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0 ,-1,-1,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[  0 ,z^4,-1 ,  0],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[   0 ,-z^4, -1 ,   0],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[z^4 ,  0,0 ,  1],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[-z^4 ,   0, 0 ,   1],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1, 0,0, 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,-1 , 0]]>;
zeta22:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta22(g)):g in G1]>;
zeta23:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1 ,0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0,  1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[  0, z^4,-1 ,  0],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[   0, -z^4,-1,    0],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[z^4 ,  0,0,   1],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[-z^4 ,   0, 0 ,   1],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0,0,  1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1,  0,0,  1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, -1,-1 , 0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0 ,-1,-1,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[   0, -z^4,-1  ,  0],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[  0, z^4,-1,   0],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[-z^4,    0,0 ,   1],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[z^4 ,  0,0 ,  1],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1 ,0,0 ,1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0,  1,-1,  0]]>;
zeta23:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta23(g)):g in G1]>;
zeta3 := map<G1 -> MatrixRing(L,2) |[Id(G1)->
[1, 0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[z^8,   0, 0 ,  1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[-z^8  ,  0,0  ,  1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[  0 ,z^8,-1 ,  0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0, 0 , 1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1 , 0,0,  1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0, -1,-1 , 0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0, -1,-1,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[-z^8,    0,0  ,  1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[z^8 ,  0,0 ,  1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[  0, z^8,-1 ,  0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1, 0,0, 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,-1 , 0]]>;
zeta3:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta3(g)):g in G1]>;
zeta31:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0  ,1,-1,  0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[-z^8 ,   0, 0 ,   1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[z^8 ,  0,0 ,  1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[   0, -z^8, -1 ,   0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[  0 ,z^8,-1 ,  0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-1,  0,0,  1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-1 , 0,0 , 1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[ 0 ,-1,-1,  0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[ 0, -1,-1,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[z^8 ,  0, 0 ,  1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[-z^8 ,   0, 0 ,   1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[  0, z^8,-1,   0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[1 ,0,0 ,1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0 , 1,-1 , 0]]>;
zeta31:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta31(g)):g in G1]>;
zeta4:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0 ,1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1,  0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[-z^4 ,   0,0 ,   1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[-z^12 ,    0, 0 ,    1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[   0, -z^4, -1 ,   0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[    0, -z^12, -1 ,    0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-z^8,    0, 0   , 1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[z^8  , 0, 0  , 1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[  0, z^8,-1 ,  0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[z^12,    0,0 ,   1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[z^4,   0,0 ,  1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[   0 ,z^12,-1,    0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[  0, z^4,-1,   0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[-1 , 0,0 , 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0, -1,-1 , 0]]>;
zeta4:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta4(g)):g in G1]>;
zeta41:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0, 1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[-z^12,     0, 0  ,   1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[-z^4 ,   0,0  ,  1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[    0, -z^12, -1  ,   0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[   0 ,-z^4,-1,    0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[z^8,   0,0,   1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-z^8 ,   0,0 ,   1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[  0 ,z^8,-1 ,  0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[z^4  , 0,0 ,  1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[z^12,    0,0 ,   1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[  0, z^4, -1 ,  0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[   0 ,z^12,-1 ,   0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[-1 , 0,0,  1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0, -1,-1 , 0]]>;
zeta41:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta41(g)):g in G1]>;
zeta42:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0, 1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0 , 1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[z^4,   0, 0 ,  1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[z^12 ,   0,0 ,   1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[  0, z^4,-1,   0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[   0, z^12,-1,    0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[-z^8 ,   0,0,    1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[z^8 ,  0,0 ,  1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[   0, -z^8,-1 ,   0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[  0, z^8,-1,   0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[-z^12 ,    0, 0  ,   1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[-z^4 ,   0,0  ,  1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[    0, -z^12,-1 ,    0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[   0 ,-z^4,-1 ,   0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[-1,  0,0 , 1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0, -1,-1 , 0]]>;
zeta42:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta42(g)):g in G1]>;
zeta43:=map<G1->MatrixRing(L,2)|[Id(G1)->
[1, 0,0, 1],
G1!(1, 2)(3, 4)(5, 6)(7, 8)(9, 10)(11, 12)(13, 14)(15, 16)->
[ 0,  1,-1 , 0],
G1!(1, 3, 5, 7, 9, 11, 13, 15)(2, 4, 6, 8, 10, 12, 14, 16)->
[z^12,    0,0 ,   1],
G1!(1, 15, 13, 11, 9, 7, 5, 3)(2, 16, 14, 12, 10, 8, 6, 4)->
[z^4 ,  0,0 ,  1],
G1!(1, 4, 5, 8, 9, 12, 13, 16)(2, 3, 6, 7, 10, 11, 14, 15)->
[   0, z^12, -1,    0],
G1!(1, 16, 13, 12, 9, 8, 5, 4)(2, 15, 14, 11, 10, 7, 6, 3)->
[  0 ,z^4, -1 ,  0],
G1!(1, 5, 9, 13)(2, 6, 10, 14)(3, 7, 11, 15)(4, 8, 12, 16)->
[z^8 ,  0, 0 ,  1],
G1!(1, 13, 9, 5)(2, 14, 10, 6)(3, 15, 11, 7)(4, 16, 12, 8)->
[-z^8  ,  0, 0 ,   1],
G1!(1, 6, 9, 14)(2, 5, 10, 13)(3, 8, 11, 16)(4, 7, 12, 15)->
[  0, z^8, -1,   0],
G1!(1, 14, 9, 6)(2, 13, 10, 5)(3, 16, 11, 8)(4, 15, 12, 7)->
[   0 ,-z^8, -1 ,   0],
G1!(1, 7, 13, 3, 9, 15, 5, 11)(2, 8, 14, 4, 10, 16, 6, 12)->
[-z^4 ,   0,0 ,   1],
G1!(1, 11, 5, 15, 9, 3, 13, 7)(2, 12, 6, 16, 10, 4, 14, 8)->
[-z^12 ,    0,  0 ,    1],
G1!(1, 8, 13, 4, 9, 16, 5, 12)(2, 7, 14, 3, 10, 15, 6, 11)->
[   0, -z^4, -1 ,   0],
G1!(1, 12, 5, 16, 9, 4, 13, 8)(2, 11, 6, 15, 10, 3, 14, 7)->
[    0 ,-z^12,-1 ,    0],
G1!(1, 9)(2, 10)(3, 11)(4, 12)(5, 13)(6, 14)(7, 15)(8, 16)->
[-1 , 0,0,  1],
G1!(1, 10)(2, 9)(3, 12)(4, 11)(5, 14)(6, 13)(7, 16)(8, 15)->
[ 0, -1,-1,  0]]>;
zeta43:=map<G1 -> MatrixRing(L,3) |[g->m1(zeta43(g)):g in G1]>;
H10,_,_:=AutomorphismGroup(L,L1);


    for h in H1 do;
        
        phi := map<G -> MatrixRing(L,3) | [g -> (h(g)^(-1)) : g in G]>; 
        A := H90(3,L,Rationals(),G,sigma,phi);  
        D := Matrix(3,3,[0,0,-1/2,0,1,0,-1/2,0,0]);  
        Q0 := Conic(D); 
        Q,_ := Conic(Transpose(A^(-1))*D*A^(-1)); 
        Q := ChangeRing(Q,Rationals());  
        boolean,_:=HasRationalPoint(Q); 
            if boolean eq true then
                 counter1:=0;counter11:=0;counter2:=0;counter21:=0;counter22:=0;counter23:=0;counter3:=0;counter31:=0;
		 counter4:=0;counter41:=0;counter42:=0;counter43:=0;
                    for g in G2 do;
                       quant:=MatrixRing(L,3)!phi(g);
                       quant1:=MatrixRing(L,3)!zeta1(psi(g)); quant11:=MatrixRing(L,3)!zeta11(psi(g));
		       quant2:=MatrixRing(L,3)!zeta2(psi(g));quant21:=MatrixRing(L,3)!zeta21(psi(g));
		       quant22:=MatrixRing(L,3)!zeta22(psi(g));quant23:=MatrixRing(L,3)!zeta23(psi(g));
		       quant3:=MatrixRing(L,3)!zeta3(psi(g));quant31:=MatrixRing(L,3)!zeta31(psi(g));
		       quant4:=MatrixRing(L,3)!zeta4(psi(g));quant41:=MatrixRing(L,3)!zeta41(psi(g));
		       quant42:=MatrixRing(L,3)!zeta42(psi(g));quant43:=MatrixRing(L,3)!zeta43(psi(g));
		                               if quant eq quant1 then 
                            counter1:= counter1+1;
                        end if;
			 if quant eq quant11 then 
                            counter11:= counter11+1;
                        end if;
 			if quant eq quant2 then 
                            counter2:= counter2+1;
                        end if;
 			if quant eq quant21 then 
                            counter21:= counter21+1;
                        end if;
 			if quant eq quant22 then 
                            counter22:= counter22+1;
                        end if;
 			if quant eq quant23 then 
                            counter23:= counter23+1;
                        end if;
 			if quant eq quant3 then 
                            counter3:= counter3+1;
                        end if;
			 if quant eq quant31 then 
                            counter31:= counter31+1;
                        end if;
			 if quant eq quant4 then 
                            counter4:= counter4+1;
                        end if;
 			if quant eq quant41 then 
                            counter41:= counter41+1;
                        end if;
 			if quant eq quant42 then 
                            counter42:= counter42+1;
                        end if;
 			if quant eq quant43 then 
                            counter43:= counter43+1;
                        end if;
			 
                    end for;
                if counter1 eq #G2 then
             		Write("16Gdata.m","zeta1");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		 if counter11 eq #G2 then
             		Write("16Gdata.m","zeta11");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter2 eq #G2 then
             		Write("16Gdata.m","zeta2");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter21 eq #G2 then
             		Write("16Gdata.m","zeta21");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter22 eq #G2 then
             		Write("16Gdata.m","zeta22");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter23 eq #G2 then
             		Write("16Gdata.m","zeta23");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter3 eq #G2 then
             		Write("16Gdata.m","zeta3");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
		
		
		
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
		
                end if;
		if counter31 eq #G2 then
             		Write("16Gdata.m","zeta31");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
		
		
		
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
		
                
                end if;
		if counter4 eq #G2 then
             		Write("16Gdata.m","zeta4");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter41 eq #G2 then
             		Write("16Gdata.m","zeta41");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter42 eq #G2 then
             		Write("16Gdata.m","zeta42");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		if counter43 eq #G2 then
             		Write("16Gdata.m","zeta43");
             
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
		 Write("16Gdata.m",g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
			
                Write("16Gdata.m",  [m2(phi(g),L):g in H10]);
                end if;
		
		Write("16Gdata.m",".....................");
            end if; 
            
    end for;  
    
    
    


