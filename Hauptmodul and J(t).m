// Magma code related to "A Classification of Genus 0 Modular curves with rational points",
// by Rakvi.
// All the functions in this file are directly taken from ModularFunctions.m available at https://math.mit.edu/~drew/SZ16/. I have made a minor modification here in the function FindHauptmodul; the variable H_ is a subgroup of H.
   
SiegelPower := recformat<a:SeqEnum, m:RngIntElt, c:FldCycElt>; 

function CuspData(H)   

/* 

     For the given subgroup H of SL(2,Z/N) with N>1, let Gamma be the congruence subgroup of level N 

     whose image modulo N is H.    

     The function returns a sequence of matrices A and a sequence of integers w.    

     The matrices A lie in SL(2,Z) and the values A*infty represent the cusps of X_Gamma.    

     The integers w gives the widths of the cusps.   

     (The first cusp will always be the one at infinity) 

*/ 

     N:=#BaseRing(H);  SL2:=SL(2,Integers(N)); 

     if SL2![-1,0,0,-1] notin H then  H:=sub<SL2| Generators(H) join {SL2![-1,0,0,-1]}>; end if; 

 

     Ht:=sub<SL2|{Transpose(g):g in Generators(H)}>; 

     cusps:=[ Sort([[Integers()!a[1],Integers()!a[2]]: a in O]) : O in Orbits(Ht)]; 

     cusps:=Sort([O: O in cusps | GCD([O[1][1],O[1][2],N]) eq 1]); 

 

     matrices:=[ SL(2,Integers())![1,0,0,1] ]; 

     for c in cusps do 

     if [1,0] notin c then 

        c_:=c[1]; 

        a:=Integers()!c_[1]; b:=Integers()!c_[2]; 

        while GCD(a,b) ne 1 do  

             if b ne 0 then a:=a+N; else b:=b+N; end if; 

        end while; 

        g,x,y:=XGCD(a,b); 

        matrices:=matrices cat [SL(2,Integers())![a,-y,b,x]];  

     end if;        

     end for; 

 

     SL2:=SL(2,Integers(N)); 

     widths:=[ Minimum([i:i in [1..N]| (SL2!A)*(SL2![1,i,0,1])*(SL2!A)^(-1) in H]) :  A in matrices]; 

     return matrices, widths; 

end function; 

function SiegelOrbits(H) 

/* 

    Given a subgroup H of SL(2,Z/NZ) with N>1, let Gamma be the congruence subgroup of level N whose image 

    in SL(2,Z/NZ) is H. 

    With notation as in the paper, computes the sequence of orbits of \pm Gamma on the set A_N. 

*/ 

    N:=#BaseRing(H);  

    AA:={[a/N,b/N] : a, b in [0..N-1] | [a,b] ne [0,0]}; 

    AA:={a: a in AA |  (0 lt a[1] and a[1] lt 1/2) or (0 eq a[1] and a[2] le 1/2) or (a[1] eq 1/2 and a[2] le 1/2) }; 

 

    SL2:=SL(2,Integers(N)); 

    if SL2![-1,0,0,-1] notin H then  H:=sub<SL2| Generators(H) join {SL2![-1,0,0,-1]}>;  end if; 

 

    orbits:=[ {[1/N*(Integers()!a[1] mod N),1/N*(Integers()!a[2] mod N)] : a in O} meet  AA : O in Orbits(H) ]; 

    orbits:=Sort([ Sort([a:a in O]) : O in orbits | #O ne 0]);     

    return orbits; 

end function; 

 

 

function SiegelDivisor(H,cusps,widths,orbit)    

//  Input: "orbit" is an orbit of H on A_N, where H is the image modulo the level N of a congruence subgroup 

//  with a list of "cusps" and their "widths". 

//  Output: the divisor (as a sequence matching the order of "cusps") of g_orbit;  see the paper for details. 

    N:=#BaseRing(H);  

    M:=RModule(Rationals(),#cusps); 

    v:=M!0; 

    for a in orbit do 

        D:=[]; 

        for i in [1..#cusps] do   

            A:=cusps[i];  w:=widths[i];  

 

            b:=[a[1]*A[1,1]+a[2]*A[2,1],a[1]*A[1,2]+a[2]*A[2,2]]; 

            b1:=b[1]-Floor(b[1]); 

            D:=D cat [6*N*w*(b1^2-b1+1/6)]; 

        end for; 

        v:=v+M!D; 

    end for;   

    return [Integers()!a: a in Eltseq(v)]; 

end function; 

function SL2ZLift(L,N) 

/* 

    Input:  a matrix L in SL(2,Z/NZ). 

    Output: a matrix in SL(2,Z) that is congruent to L mod N. 

*/ 

    Z:= Integers(); 

    GL2 := GeneralLinearGroup(2,Z);  

    SL2_N := SpecialLinearGroup(2,Integers(N)); 

 

    L := SL2_N!L;   //Coerce just in case 

    a := Z!L[1,1]; b := Z!L[1,2]; c := Z!L[2,1]; d := Z!L[2,2]; 

    g, x, y := Xgcd(a,b);    

    if g eq 1 then 

        D := x*(1-(a*d-b*c)) div N; 

        C :=-y*(1-(a*d-b*c)) div N;  

        A:=[a,b,c+N*C,d+N*D]; 

    elif (b mod N) eq 0 and (c mod N) eq 0 then 

        A := Solution(d, (1-a*d) div N, N); 

        B := (A*d - ((1-a*d) div N)) div N; 

        A:=[a+N*A, N*B, N, d]; 

    else 

            h := Solution(g,1,N);  

            L1:= $$([g,0,0,h],N);  L2:= $$([a div g, b div g, g*c, g*d],N); 

            A := (GL2!L1)*(GL2!L2); 

            A:=[A[1,1],A[1,2],A[2,1],A[2,2]]; 

        end if; 

      

        //Check! 

        assert A[1] mod N eq L[1,1] and A[2] mod N eq L[1,2] and A[3] mod N eq L[2,1] and A[4] mod N eq L[2,2]; 

        assert A[1]*A[4]-A[2]*A[3] eq 1; 

 

        return A; 

end function;
function ReduceKlein(a,c) 

/*  Input: A pair a in Q^2-Z^2 and a constant c. 

    Output: A constant C and a "reduced" pair b in Q^2-Z^2 such that c*k_a(z) = C*k_b(z), 

            where k_a(z) is a Klein form. 

*/ 

    b1:=Floor(a[1]); b2:=Floor(a[2]); 

    a1:=a[1] - b1; a2:=a[2] - b2; 

    m:=(b2*a1-b1*a2)/2;  

    e:=(-1)^(b1+b2+b1*b2)*RootOfUnity(Denominator(m))^Numerator(m); 

 

    if ((0 lt a1) and (a1 lt 1/2) and (0 le a2) and (a2 lt 1)) or 

       ((a1 eq 0) and (0 lt a2) and (a2 le 1/2)) or 

       ((a1 eq 1/2) and (0 le a2) and (a2 le 1/2)) then 

       return c*e, [a1,a2]; 

    end if; 

 

    return $$([-a1,-a2],-c*e); 

end function; 
 

function DedekindFactor(A) 

/*   

    For a matrix A in SL(2,Z) with last row (c,d), returns the 12-th root of unity such that 

    eta(Az)^2= w*(cz+d)*eta(z)^2, where eta is the Dedekind eta function. 

*/ 

    C<w>:=CyclicGroup(12); 

    SL2:=SL(2,Integers(12));  

    SL2:=sub<SL2|[[1,1,0,1],[0,1,-1,0]]>; 

    f:=hom<SL2->C|[w^1,w^3]>; 

    i:=[i: i in [0..11] | f( SL2!A) eq w^i][1]; 

    return RootOfUnity(12)^i;   

end function; 


function ActOnSiegel(g,A :d:=1)   

/*  A is a matrix in GL(2,Z) and d an integer. 

    If g is a record of type SiegelPower, representing a function c*g_a^m with g_a a Siegel function,  

    then the function returns a record of the same type representing sigma_d(g)|_A.   

    [the return function c'*g_{a'}^m has "reduced" a', i.e., a' lies in some set A_N (as in the paper).] 

    If g is a sequence, then returns sequence with "ActOnSiegel( ,A,d:=d)" applied to its elements.    

 

    Warning: It is assumed that d is relatively prime to the denominators of a=(a1,a2) and to 2 and 3. 

*/ 

 

    if Type(A) eq SeqEnum then 

       R:=Parent(A[1]);  

       A:=GL(2,R)!A; 

    end if; 

    R:=BaseRing(Parent(A)); 

    if Type(R) ne RngInt then 

       N:=#R; 

       d:=Integers()!Determinant(A); while GCD(d,6) ne 1 do d:=d+N; end while; 

       B:=(GL(2,Integers(N))![1,0,0,d])^(-1) * A; 

       B:=SL(2,Integers())!SL2ZLift(B,N); 

       return $$(g,B :d:=d); 

    end if; 

 

    if Type(g) eq SeqEnum then return [$$(s,A: d:=d): s in g]; end if; 

    

    if d ne 1 then  

       g:=rec<SiegelPower|a:=[g`a[1],d*g`a[2]], m:=g`m, c:=Conjugate(g`c,d)>; 

       return $$(g,A: d:=1); 

    end if; 

 

    A    :=SL(2,Integers())!A; 

    a    :=g`a;  

    c_,a_:=ReduceKlein([a[1]*A[1,1]+a[2]*A[2,1],a[1]*A[1,2]+a[2]*A[2,2]],1);  

    C    :=g`c * (DedekindFactor(A) * c_)^(g`m); 

    return rec<SiegelPower|a:=a_, m:=g`m, c:=C>; 

end function; 

function FindHauptmodul(H,H_)
/*  Let H be the image modulo the level N of a congruence subgroup Gamma of genus 0; assume that N is not 1 or 11.
    Returns a hauptmodul for H as described in the paper; output format described in "ComputeHauptmoduls.txt".
*/

   
    N:=#BaseRing(H); 
    SL2:=SL(2,Integers(N)); 

    // Compute cusps and the Siegel divisors of X_Gamma
    cusps, widths := CuspData(H);      
    // Compute the orbits of Gamma on A_N
    orbits:=SiegelOrbits(H);    
    divisors:=[SiegelDivisor(H,cusps,widths,O):O in orbits];

    if #cusps ge 2 then 
       A:=Transpose( Matrix([ Eltseq(D) : D in divisors]) );      
       // Transposes needed because of how Magma does linear algebra.
       b0:=Matrix([[0]: j in [1..#cusps]]);
       b:=b0; b[1][1]:=-12*N;  b[2][1]:=+12*N;
       _,m,W:=IsConsistent(Transpose(A),Transpose(b));
       m:=Eltseq(m);

       haupt:=[];
       for j in [1..#orbits] do
           if m[j] ne 0 then
           for a in orbits[j] do
               haupt:=haupt cat [rec<SiegelPower|a:=a,m:=m[j],c:=CyclotomicField(1)!1>];
           end for;
           end if;
       end for;

       e:=&+[m[j] * &+[a[2]*(a[1]-1)/2: a in orbits[j]]   : j in [1..#orbits]];
       c:=RootOfUnity(Denominator(e))^(-Numerator(e)); if Type(c) eq FldRatElt then c:=CyclotomicField(2)!c; end if;
       haupt[1]`c:=c;
    end if;


    if #cusps eq 1 then
       D := sub<SL2|[[1,0,0,1]]>;
       haupt_:=FindHauptmodul(H_,D); //D is a dummy variable here.
       T:=Transversal(H,H_);
       T:=[SL2ZLift(A,N): A in T];

       haupt:=[];
       for A in T do
          h_:=[];
          for r in haupt_ do
              h_:=h_ cat [ActOnSiegel(r,A)];
          end for;
          haupt:=haupt cat [h_];          
       end for;
    end if;

     
   
        
    return haupt;
end function;


 function SiegelExpansion(g,Precision) 

/*  Computes the q-expansion of g.   We assume that g is given in the format as described above for "hauptmodul" for 

    the record format "CongSubgroup".  The quantity Precision determines how many terms are used in the product  

    giving the Siegel functions that occur. 

 

    Warning: We will assume that a is "reduced" for each Siegel function g_a, i.e., it occurs in some set A_N from the paper. 

*/ 

        if Type(g) eq SeqEnum and Type(g[1]) eq SeqEnum then 

           return &+[$$(b,Precision) : b in g]; 

        end if; 

 

        e:=&+[r`a[2]*(r`a[1]-1)/2 * r`m : r in g]; 

        NN:=LCM( [Denominator(r`a[2]): r in g] cat [Denominator(e)]); 

 

        c:=&*[r`c: r in g]; 

        K:=Compositum(CyclotomicField(NN),Parent(c));     

        c:=K!c; 

 

        R<q>:=PuiseuxSeriesRing(K); 

        gg:= R!(RootOfUnity(Denominator(e))^Numerator(e));  

        gg:=gg* &*[ (1-q^r`a[1]*(R!(RootOfUnity(Denominator(r`a[2])))^Numerator(r`a[2])) +O(q^Precision))^r`m : r in g];   

 

        S:=[1] cat  

           &cat[ [(1-q^n * q^r`a[1]*(R!(RootOfUnity(Denominator(r`a[2])))^Numerator(r`a[2])) +O(q^Precision))^r`m : n in [1..Floor(Precision-r`a[1])]] : r in g];   

        S:=S cat  

           &cat[ [(1-q^n * q^(-r`a[1])*(R!(RootOfUnity(Denominator(r`a[2])))^Numerator(-r`a[2]) )+O(q^Precision))^r`m : n in [1..Floor(Precision+r`a[1])]] : r in g];             

        gg:=gg*&*S; 

 

        v:=&+[1/2*(r`a[1]^2-r`a[1]+1/6)*r`m : r in g];  

        gg:=gg* &*[(-1)^r`m: r in g] * q^v; 

 

        return R!(c*gg); 

end function; 
 function FindRelation(h,j,n) 

 

/* Let h and j be Puiseux series with coefficients in a field K such that 

   K(h) is a degree n extension of K(j).   We thus have j=J(h) for a unique  

   rational function J(t) in K(t); it has degree n. 

   The function outputs J(t). 

 

   Warning: An error will occur if there are not enough terms of h and j to determine J. 

*/ 

        K:=Compositum(BaseRing(Parent(h)),BaseRing(Parent(j))); 

    P<[a]>:=PolynomialRing(K,2*(n+1)); 

    R<q>:=PuiseuxSeriesRing(P); 

        h:=R!h; j:=R!j; 

    s:= j*&+[a[i+1]*h^i : i in [0..n]] - &+[a[i+n+2]*h^i : i in [0..n]]; 

    A:=[];   

    repeat 

        v:=Valuation(s);c:=P!Coefficient(s,v);    

            s:=s-c*q^v; 

        A:= A cat [ [K!MonomialCoefficient(c,a[i]) : i in [1..2*n+2]] ];     

        B:=Matrix(K,A); 

        until Rank(B) eq 2*n+1; 

        v:=Basis(NullSpace(Transpose(B)))[1]; 

        _<t>:=FunctionField(K); 

        return (&+[v[i+n+2]*t^i : i in [0..n]])/(&+[v[i+1]*t^i : i in [0..n]]);        

end function; 

 




