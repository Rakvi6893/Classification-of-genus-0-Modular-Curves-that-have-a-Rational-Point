 load "Hauptmodul and J(t).m";
function SigmaJ(J,g) 

/* Input : A function J(t) which is an element in field K(t) and g which is in Gal(K/Q) 

Output : A function sigma(J(t)) where sigma acts as follows, it fixes t and acts on coefficients.*/ 

 

K:=BaseRing(Parent(J));  

G,iota,sigma:=AutomorphismGroup(K); 

g := G!g; 

P<t> := PolynomialRing(K); 

Num := P ! Numerator(J); 

Den := P ! Denominator(J); 

A := [sigma(g)(Coefficient(Num,i)) : i in [0..Degree(Num)]]; 

B := [sigma(g)(Coefficient(Den,i)) : i in [0..Degree(Den)]]; 

J1:=0; 

for i in [0..Degree(Num)] do; 

    J1 := J1+ (A[i+1]*(t^i)); 

end for; 

J2 :=0; 

for i in [0..Degree(Den)] do; 

    J2 := J2+ (B[i+1]*(t^i)); 

end for; 

return J1/J2; 

end function; 

function EvaluateRationalFunction(f,a)
/* Input: f a rational function in some K(t), a is an element of K or a pair giving a point in P^1(K).
   The function returns f(a) as a pair representing a point in P^1(K); it is [1,0] or of the form [x,1].
*/
    if Type(a) ne SeqEnum then a:=[a,1]; end if;

    num:=Numerator(f);  den:=Denominator(f);  d1:=Degree(num); d2:=Degree(den);
    if a[2] eq 0 and d1 gt d2 then return [1,0]; end if;
    if a[2] eq 0 and d1 lt d2 then return [0,1]; end if;
    if a[2] eq 0 and d1 eq d2 then return [Coefficient(num,d1)/Coefficient(den,d2),1]; end if;  
    
    a:=a[1]/a[2];
    if Evaluate(den,a) eq 0 then return [1,0]; end if;
    return [Evaluate(num,a)/Evaluate(den,a), 1];
end function;


function RationalInverse(f)    
/*  For a rational function f in K(t) of degree 1 computes g in K(t) so that g(f(t))=t=f(g(t)).
*/
    K:=BaseRing(Parent(f));
    F<t>:=FunctionField(K); f:=F!f;
    b:= Evaluate(Numerator(f),0);    a:= Evaluate(Numerator(f)-b,1);
    d:= Evaluate(Denominator(f),0);  c:= Evaluate(Denominator(f)-d,1);
    return (d*t-b)/(-c*t+a);
end function;


function RationalMap0(a,b,c,K)
/*  Given three distinct elements a,b,c in P^1(K) gives the unique degree 1 rational function
    in K(t) such that the induced map P^1 -> P^1 takes a to 0, b to 1 and c to infinity. 
    We can take a,b,c to be a non-zero pair in K^2 or a number d in K meaning [d,1].  The 
    point at infinity is [1,0].
*/
    if Type(a) ne SeqEnum then a:=[a,1]; end if;
    if Type(b) ne SeqEnum then b:=[b,1]; end if;
    if Type(c) ne SeqEnum then c:=[c,1]; end if;

    F<t>:=FunctionField(K);
    if c[2] eq 0  then a:=a[1]/a[2]; b:=b[1]/b[2];  return (t-a)/(b-a); end if;
    if b[2] eq 0  then a:=a[1]/a[2]; c:=c[1]/c[2];  return (t-a)/(t-c); end if;
    if a[2] eq 0  then b:=b[1]/b[2]; c:=c[1]/c[2];  return (b-c)/(t-c); end if;
    a:=a[1]/a[2]; b:=b[1]/b[2]; c:=c[1]/c[2];       return (t-a)/(t-c)*(b-c)/(b-a);    
end function;


function RationalMap(a,b,c,aa,bb,cc,K)
/* Input: Distinct a,b,c in P^1(K) and distinct aa,bb,cc in P^1(K) with K a field.          
    Output: The unique rational function in K(t) that induces an isomorphism 
          P^1 -> P^1 which takes a,b,c to aa,bb,cc, respectively.
*/
    F<t>:=FunctionField(K);
    f1:=RationalMap0(a,b,c,K);
    f2:=RationalMap0(aa,bb,cc,K);
    return Evaluate(RationalInverse(f2),f1);
end function;


function FindParametrization(J,a,K)
/*
    Input:  a rational function J(t) in K(t) and a triple a=(a1,a2,a3) of distinct
            elements in Q such that there is some invertible f in K(t) such that
            J(f(t)) belongs to Q(t) and a_1,a_2,a_3 belong in J(f(Q)).  
            [We assume that J(infty) is not a_1,a_2 or a_3]
    Output: J(f(t)) for some f as above.
*/
    F<t>:=FunctionField(K);
    J:=F!J; a:=[K!b: b in a];
    R:=[ [r[1]: r in Roots(Numerator(J-a[i]))] : i in [1..3]];
    Js:={};
    for a in R[1], b in R[2], c in R[3] do
        f:=RationalMap(0,1,[1,0], a,b,c, K);
        JJ:=Evaluate(J,f);
        if JJ in FunctionField(Rationals()) then
            return JJ;
        end if;        
    end for;
    return 0;
end function;


function ValuationRationalFunction(f,P)
/*
    Give a non-zero rational function f  in K(t) returns the valuation at the point P.
*/
    K:=BaseRing(Parent(f));
    if Type(P) ne SeqEnum then 
       return ValuationRationalFunction(f,[P,1]);
    end if;

    if P[2] eq 0 then
       return Degree(Denominator(f))-Degree(Numerator(f));
    end if;

    a:=K!(P[1]/P[2]);
    Pol<t>:=PolynomialRing(K);
    n:=Pol!Numerator(f); d:=Pol!Denominator(f);

    return Valuation(n,t-a)-Valuation(d,t-a);
end function;



function SameRationalParametrization(J1,J2,K : findall:=true, triple:=[]);
/*
    Input:  J1, J2 non-constant elements of K(t)
    Output: Returns true if J1(t) = J2(f(t)) for some f in K(t) of degree 1; otherwise false.
            If true, the also outputs f (returns the set of all possible f if "findall" is true).
    Note: f is searched for by solving J1(a)=J2(f(t)) for three different a in P^1(K); the three
          values used can be set by changing "triple".
*/
    F<t>:=FunctionField(K);
    J1:=F!J1; J2:=F!J2;

    if #triple ge 3 then
       triple:=[triple[i]: i in [1..3]];
    else
       triple:=[[1,0],[0,1],[1,1]];
    end if;

    RR:=[];
    for i in [1..3] do
        P:=triple[i];  if Type(P) ne SeqEnum then P:=[P,1]; end if;
        v:=ValuationRationalFunction(J1,P);

        Q:=EvaluateRationalFunction(J1,P);
        if Q[2] ne 0 then
           num:=Numerator(J2-Q[1]/Q[2]); den:=Denominator(J2-Q[1]/Q[2]); 
        else
           num:=Numerator(J2); den:=Denominator(J2); 
        end if;

        R:=[[r[1],1]: r in Roots(num) cat Roots(den)] cat [[1,0]];
        R:=[r: r in R | ValuationRationalFunction(J2,r) eq v];

        if #R eq 0 then return false; end if;

        RR:=RR cat [R];
    end for;

     
    F:={};
    for a in RR[1], b in RR[2], c in RR[3] do
    if #{a,b,c} eq 3 then
        f:=RationalMap(triple[1],triple[2],triple[3], a,b,c, K);
        if Evaluate(J2,f) eq J1 then 
           F:=F join {f};
           if findall eq false then 
              return true, f; 
           end if;
        end if;
    end if;
    end for;   

    if #F eq 0 then return false; end if;
    return true, F;
end function;

 function H90(n,L,K,G,sigma,xi)   

 // Input: xi: G=Gal(L/K)-> GL(n,L) 1-cocycle.   
// Output: matrix A in GL(n,L) such that xi_g = A^(-1) g(A) for all g in G. 
// Also contains a commented code to perform LLL on A obtained.

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

 

    // LLL of A to make the maps look nicer! If the user wants to use this feature, just uncomment the code.
    /*AQ:=[];
    for i in [1..n] do;
    for j in [1..n] do;
        AQ:= AQ cat Eltseq(A[i,j]);
    end for;
    end for;
    AQ:=Matrix(K,n,n*Degree(L),AQ);
    Latt:=LLL(AQ);

    Ared:=[];
    for i in [1..n] do;
        for j in [1..n] do;
        Ared:= Ared cat [L![Latt[i,k]: k in [(Degree(L)*(j-1)+1)..Degree(L)*j]]];
    end for;
    end for;
    Ared:=Matrix(L,n,n,Ared);*/




    // Check:

    for g in G do

        gA:=Matrix([ [sigma(g)(A[i,j]):j in [1..n]] : i in [1..n]]);

        assert A^(-1)*gA eq xi(g); 

    end for;

    
    return A;
 

end function; 



function check(xi,M) 
// Checks if the given map xi: G -> GL(3,L) is a cocycle.
    

    L := CyclotomicField(M); 

    G,iota,sigma:=AutomorphismGroup(L); 

    R := MatrixRing(L,3); 

    action := hom<G -> Aut(R)|g :-> iso<R->R | A :-> [[(sigma(g))(A[i,j]): j in [1..Ncols(A)]] : i in [1..Nrows(A)] ]>>;
    n :=0; 

    for g in G do; 

        for h in G do; 

        

            if xi(g)*(action(g)(xi(h))) eq xi(g*h) then; 

                n:=n+1; 

            end if; 

     

        end for; 

    end for; 

    if n eq Order(G)^2 then; 

        return true; 

    else 

        return false; 

    end if; 

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

function Act(g,A,f,h) 

/* Input : Matrix A and g, where g is a degree 1 function. 

Output : A*(g(u)); The action * is the action of GL_2(Z/NZ) on field of modular functions F_N. */ 

 

N:=#BaseRing(Parent(A)); 

K:=CyclotomicField(N); 

F<t>:=FunctionField(K); 

R<q>:=PuiseuxSeriesRing(K); 

d:=Integers()!Determinant(A); 

g := F!g; 

f := F!f; 

s := Evaluate(g,f); 

num:=Numerator(s); den:=Denominator(s); 

s_d:=( Conjugate(Coefficient(num,1),d) *t + Conjugate(Coefficient(num,0),d) ); 

s_d:=s_d/( Conjugate(Coefficient(den,1),d) *t + Conjugate(Coefficient(den,0),d) ); 

hA:=ActOnSiegel(h, A);

return s_d,hA; 

 

end function; 
