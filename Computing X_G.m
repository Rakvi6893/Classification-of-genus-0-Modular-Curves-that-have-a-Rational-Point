// Magma code and data related to "Genus 0 Modular curves with rational points",
// by Rakvi.


// Computes X_G coming from genus 0 congruence subgroups X_{\Gamma}

Vgroup := recformat<N:RngIntElt, label:MonStgElt, gens, index:RngIntElt, G:GrpMat, hauptmodul,h:RngSerPuisElt, JG:FldFunRatUElt,A,sub :SeqEnum, sup :SeqEnum,AG>;
Agroup := recformat<N:RngIntElt, label:MonStgElt, gens, index:RngIntElt, G:GrpMat, hauptmodul,h:RngSerPuisElt, JG:FldFunRatUElt,A,sub :SeqEnum, sup :SeqEnum,AG>;

/* Record for a congruence subgroup Gamma of genus 0.
   N:              level of G
   label:          label of G.
   G:              image of G in GL_2(Z/NZ).
   gens:           generators for subgroup G of GL_2(Z/NZ).
   index:          index of G in GL_2(Z/NZ).
   hauptmodul:      hauptmodul from H.
   h:              q-expansion for the hauptmodul from H.   
   JG:              rational function such that JG(Ah) is the modular j-invariant.
   A:             Matrix in MatrixRing(K_N,2) such that xi(\sigma)=A^(-1)\sigma(A) where xi is a 1-cocycle from Gal(K_N/Q) -> PGL_2(K_N) from which G comes.
   
   sub:            
    sup: 
    AG :          Group of f such that JG=JG(f)           
*/
   

            


load "Congruence Subgroups.m";
load "Rational Functions.m";


VGlist:=AssociativeArray();

keys:=[k: k in Keys(CPlist)];
level:=[CPlist[k]`N:k in keys];
ParallelSort(~level,~keys);


// Here we find a pair (PP^1,\pi_1) which is isomorphic to (X_{\Gamma},\pi_{\Gamma}) at some N.

for k in keys do;
    
    if k eq "1A" then continue; end if;
   
    
   
    N := CPlist[k]`N; 
    
   
    if k eq "5F" then
        N:=15;
        
    end if;
    
    if k eq "16F" then
        N:=32;
    end if;
    if k eq "8E" or k eq "8K" then
        N:=16;
    end if;
     L := CyclotomicField(N); 
     S<t> := FunctionField(L); 

    if CPlist[k]`J in FunctionField(Rationals()) then
        
        _,AG:=SameRationalParametrization(CPlist[k]`J,CPlist[k]`J,L);
        VGlist[k]:= rec<Vgroup | N:=CPlist[k]`N,  label:=CPlist[k]`label, hauptmodul:=CPlist[k]`hauptmodul,h:=CPlist[k]`h, JG:=CPlist[k]`J,A:=Matrix(L,2,2,[1,0,0,1]),AG:=AG>;
        
        
        continue;
    end if;
    J := CPlist[k]`J;
    J := S!J;
    G,iota,sigma:=AutomorphismGroup(L); 
    R := MatrixRing(L,2); 
    action := hom< G -> Aut(R) | g :-> iso< R -> R | n :-> [sigma(g)(n[1,1]),sigma(g)(n[1,2]),sigma(g)(n[2,1]),sigma(g)(n[2,2])] > >; 
    Ggens:=Generators(G); 

    C := AssociativeArray(); 

    n:=1; 

    for g in Ggens do; 

        if SameRationalParametrization(SigmaJ(J,g),J,L) eq false then 

         

            C[g]:={}; 

            n:=0; 

        else 

            _,C[g]:=SameRationalParametrization(SigmaJ(J,g),J,L); 

            n:=n*#C[g]; 

        end if; 

  

    end for; 

 

    if n eq 0 then  

       
        
        
        continue;
        

    end if; 

    M :={}; 

    while #M ne n do; 

        xi :=[g->S!Random(C[g]):g in Ggens]; 

        M:= M join {xi}; 

    end while; 

 

    Setcoc:={}; 

    m1 := map< MatrixRing(L,2) -> MatrixRing(L,3) | n :-> (1/Determinant(n))*Matrix(3,3,[n[1,1]^2,2*n[1,1]*n[1,2],n[1,2]^2,n[1,1]*n[2,1],n[1,1]*n[2,2]+n[1,2]*n[2,1],n[1,2]*n[2,2],n[2,1]^2,2*n[2,1]*n[2,2],n[2,2]^2])>;  

    if #Ggens eq 1 then 

     for m in M do; 

             

            xi0:=AssociativeArray(); 

        for i in [1..Order(G.1)] do; 

             

            if i eq 1 then 

                xi0[1]:=R![Evaluate(Numerator(m[1][2])-Evaluate(Numerator(m[1][2]),0),1),Evaluate(Numerator(m[1][2]),0),Evaluate(Denominator(m[1][2])-Evaluate(Denominator(m[1][2]),0),1),Evaluate(Denominator(m[1][2]),0)]; 

            else 

                xi0[i]:=R!((xi0[1])*(action(G.1)(xi0[i-1]))); 

 

            end if; 

             

        end for; 

        xi:=map<G-> MatrixRing(L,3) |[(G.1)^i-> m1(xi0[i]):i in [1..Order(G.1)]]>; 

 

                if check(xi,N) eq true then  

            Setcoc:=Setcoc join {xi}; 

        end if; 

    end for; 

    end if; 

 

if #Ggens eq 2 then 

for m in M do; 

    g1:=m[1][1]; 

    g2:=m[2][1]; 

    xi0:=AssociativeArray(); 

    for i in [1..Order(g1)] do; 

        if i eq 1 then 

                xi0[g1]:=R![Evaluate(Numerator(m[1][2])-Evaluate(Numerator(m[1][2]),0),1),Evaluate(Numerator(m[1][2]),0),Evaluate(Denominator(m[1][2])-Evaluate(Denominator(m[1][2]),0),1),Evaluate(Denominator(m[1][2]),0)]; 

            else 

                xi0[(g1)^i]:=R!((xi0[g1])*(action(g1)(xi0[(g1)^(i-1)]))); 

 

         end if; 

             

      end for; 

 

    for j in [1..Order(g2)] do; 

        if j eq 1 then 

                xi0[g2]:=R![Evaluate(Numerator(m[2][2])-Evaluate(Numerator(m[2][2]),0),1),Evaluate(Numerator(m[2][2]),0),Evaluate(Denominator(m[2][2])-Evaluate(Denominator(m[2][2]),0),1),Evaluate(Denominator(m[2][2]),0)]; 

            else 

                xi0[(g2)^j]:=R!((xi0[g2])*(action(g2)(xi0[(g2)^(j-1)]))); 

 

         end if; 

             

      end for; 

 

    for i in [1..Order(g1)] do; 

        for j in [1..Order(g2)] do; 

            xi0[((g1)^i)*(g2^j)]:=R!((xi0[(g1)^i])*(action((g1)^i)(xi0[(g2)^(j)]))); 

         end for; 

    end for; 

 

xi:=map<G->MatrixRing(L,3)|[g ->m1(xi0[g]) : g in G]>; 

                if check(xi,N) eq true then  

                    Setcoc:=Setcoc join {xi}; 

                end if; 

end for; 

end if; 

 

 

if #Ggens eq 3 then 

 

for m in M do; 

    g1:=m[1][1]; 

    g2:=m[2][1]; 

    g3:=m[3][1]; 

    xi0:=AssociativeArray(); 

    for i in [1..Order(g1)] do; 

        if i eq 1 then 

                xi0[g1]:=R![Evaluate(Numerator(m[1][2])-Evaluate(Numerator(m[1][2]),0),1),Evaluate(Numerator(m[1][2]),0),Evaluate(Denominator(m[1][2])-Evaluate(Denominator(m[1][2]),0),1),Evaluate(Denominator(m[1][2]),0)]; 

            else 

                xi0[g1^i]:=R!((xi0[g1])*(action(g1)(xi0[(g1)^(i-1)]))); 

 

         end if; 

             

      end for; 

 

    for j in [1..Order(g2)] do; 

        if j eq 1 then 

                xi0[g2]:=R![Evaluate(Numerator(m[2][2])-Evaluate(Numerator(m[2][2]),0),1),Evaluate(Numerator(m[2][2]),0),Evaluate(Denominator(m[2][2])-Evaluate(Denominator(m[2][2]),0),1),Evaluate(Denominator(m[2][2]),0)]; 

            else 

                xi0[g2^j]:=R!((xi0[g2])*(action(g2)(xi0[(g2)^(j-1)]))); 

 

         end if; 

             

      end for; 

     

    for k in [1..Order(g3)] do; 

        if k eq 1 then 

                xi0[g3]:=R![Evaluate(Numerator(m[3][2])-Evaluate(Numerator(m[3][2]),0),1),Evaluate(Numerator(m[3][2]),0),Evaluate(Denominator(m[3][2])-Evaluate(Denominator(m[3][2]),0),1),Evaluate(Denominator(m[3][2]),0)]; 

            else 

                xi0[g3^k]:=R!((xi0[g3])*(action(g3)(xi0[(g3)^(k-1)]))); 

 

         end if; 

             

      end for; 

 

    for i in [1..Order(g1)] do; 

        for j in [1..Order(g2)] do; 

             

            xi0[((g1)^i)*(g2^j)]:=R!((xi0[g1^i])*(action(g1^i)(xi0[(g2)^(j)]))); 

         end for; 

    end for; 

 

         

for i in [1..Order(g1)] do; 

        for k in [1..Order(g3)] do; 

             

            xi0[((g1)^i)*(g3^k)]:=R!((xi0[g1^i])*(action(g1^i)(xi0[(g3)^(k)]))); 

         end for; 

    end for; 

for j in [1..Order(g2)] do; 

        for k in [1..Order(g3)] do; 

             

            xi0[((g2)^j)*(g3^k)]:=R!((xi0[g2^j])*(action(g2^j)(xi0[(g3)^(k)]))); 

         end for; 

    end for; 

 

for i in [1..Order(g1)] do; 

        for j in [1..Order(g2)] do; 

           for k in [1..Order(g3)] do;  

            xi0[((g1)^i)*(g2^j)*(g3^k)]:=R!((xi0[g1^i])*(action(g1^i)(xi0[(g2^j)*(g3^k)]))); 

         end for; 

    end for; 

end for; 

        xi:=map<G->MatrixRing(L,3)|[g ->m1(xi0[g]) : g in G]>; 

 

 

                if check(xi,N) eq true then  

            Setcoc:=Setcoc join {xi}; 

        end if; 

    end for; 

 

end if; 
countercoc:=0;
    for phi in Setcoc do;
        countercoc:=countercoc+1;
        A := H90(3,L,Rationals(),G,sigma,phi);  

        D := Matrix(3,3,[0,0,-1/2,0,1,0,-1/2,0,0]); // this is the matrix corresponding to y^2-xz 

        Q0 := Conic(D); 

        Q,_ := Conic(Transpose(A^(-1))*D*A^(-1)); 
    

        Q := ChangeRing(Q,Rationals());  
        if HasRationalPoint(Q) eq false then 
            continue; 
    
        else
            
            B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 

            B := B^(-1); 

            C := m2(B*A,L); 

            C := C^(-1); 
    
            g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 

            JG:=Evaluate(J,g);
            assert JG in FunctionField(Rationals()); 
            _,AG:=SameRationalParametrization(JG,JG,L);
             // checking if each element of AG lies in FunctionField(Rationals()); if yes, then we continue;
            countAG:=0;
            for f in AG do;
               if f in FunctionField(Rationals()) then
                  countAG:=countAG+1;
               end if;
            end for;
            if countAG eq #AG  or countercoc eq #Setcoc then
        
        
        
            VGlist[k]:= rec<Vgroup | N:=N,  label:=CPlist[k]`label, hauptmodul:=CPlist[k]`hauptmodul,h:=CPlist[k]`h, JG:=JG,A:=C^(-1),AG:=AG>;
            break;
            end if;
            end if;
            

    end for;
    
    
end for;

Alllist:=AssociativeArray();
keys:=[k: k in Keys(VGlist)];
level:=[VGlist[k]`N:k in keys];
ParallelSort(~level,~keys);
for k in keys do;
    
    
    Alllist[k]:=AssociativeArray();
    
    // checking if each element of AG lies in FunctionField(Rationals()); if yes, then we continue;
    n:=0;
    for f in VGlist[k]`AG do;
        assert f in FunctionField(CyclotomicField(CPlist[k]`N));
        if f in FunctionField(Rationals()) then
            n:=n+1;
        end if;
    end for;
    if n eq #(VGlist[k]`AG) then
        Alllist[k][1]:=VGlist[k];
        
        continue;
    end if;

    
    // calculating b that gives an upper bound for number of cocycles
    SL2:=SL(2,Integers(CPlist[k]`N));
    N:= Normalizer(SL2,CPlist[k]`H);
    N1:=quo<N|CPlist[k]`H>;
    s:=[];
    for n in N1 do;
        x:=0;
        t:=Factorisation(Order(n));
        // checking if for every p|Order(n) does p|CPlist[k]`N
        for p in t do;
            if CPlist[k]`N mod p[1] eq 0 then x:=x+1; end if;
        end for;
        if x eq #t then s:=s cat [Order(n)];end if;
    end for;
    b:=Lcm(s);
    if k eq "48A" then b:=1;end if;
    
   
    if ((CPlist[k]`N) mod 2 eq 0 ) and ((CPlist[k]`N) mod 4 ne 0) then
        b:=2*b;
    end if;
    
    if k eq "30A" then b:=4;end if;
    
    L := CyclotomicField((CPlist[k]`N)*b); 
    S<t> := FunctionField(L); 
    
    JG:=VGlist[k]`JG; 
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
   
    j:=0;
    for h in H1 do;
        j:=j+1; 
        phi := map<G -> MatrixRing(L,3) | [g -> (h(g)^(-1)) : g in G]>; 
        A := H90(3,L,Rationals(),G,sigma,phi);  
        D := Matrix(3,3,[0,0,-1/2,0,1,0,-1/2,0,0]);  
        Q0 := Conic(D); 
        Q,_ := Conic(Transpose(A^(-1))*D*A^(-1)); 
        Q := ChangeRing(Q,Rationals());  
        boolean,_:=HasRationalPoint(Q); 
            if boolean eq false then
                continue; 

            else 
                B := Transpose(ParametrizationMatrix(Q)); //Transpose to make it left action 
                B := B^(-1); 
                C := m2(B*A,L); 
                C := C^(-1); 
                g := (C[1,1]*t+C[1,2])/(C[2,1]*t+C[2,2]); 
                ginv:=RationalInverse(g);
                J1:=  Evaluate(JG,g); assert J1 in FunctionField(Rationals()); 
                // checking the level of G
                A:= C^(-1)*(MatrixRing(L,2)!VGlist[k]`A);
                AG1:={};
                for f in AG do;
                  AG1:= AG1 join {Evaluate(ginv,Evaluate(f,g))};
                end for;  
               // _,AG1:=SameRationalParametrization(J1,J1,L);
                for i in [1..b] do;
                    if A in MatrixRing(CyclotomicField((CPlist[k]`N)*i),2) then
                        Alllist[k][j]:=rec<Agroup | N:=(CPlist[k]`N)*i,  label:=CPlist[k]`label, hauptmodul:=CPlist[k]`hauptmodul,h:=CPlist[k]`h, JG:=J1,A:=A,AG:=AG1>;
                        
                    else continue;
                    end if;
                 break;   
                end for;
            end if; 
            
    end for;  
    
    
    
end for;



