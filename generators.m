// Magma code and data related to "Genus 0 Modular curves with rational points",
// by Rakvi.


// Code for computing a set of generators for genus 0 group G; we use this to compute for groups in Theorem 1.2


load "Computing X_G.m";
SetOutputFile("Data.m":Overwrite:=true);

keys:=[k: k in Keys(VGlist)];
level:=[VGlist[k]`N:k in keys];
ParallelSort(~level,~keys);

// We will compute generators for the groups we have produced

for k in keys do;
    //Write("Data.m",k);
    subkeys:=[k1: k1 in Keys(Alllist[k])]; 
    for j in subkeys do;
        
        Gamma:=Alllist[k][j];
        M := Gamma`N;
        L := CyclotomicField(M);
        F<t>:=FunctionField(L);
        R<q>:=PuiseuxSeriesRing(L);
        h := Gamma`hauptmodul; 
        A:= Gamma`A;
        A:= MatrixRing(L,2)!A;
        f := (A[1,1]*t+A[1,2])/(A[2,1]*t+A[2,2]); 
        J := Gamma`JG; 
        prec:=20;
        SL2 := SL(2,Integers(M)); 
        GL2:=GL(2,Integers(M));
        U:=UnitGroup(Integers(M));
        H_:= CPlist[k]`H;
        SL2_:=SL(2,Integers(CPlist[k]`N));
        red:=hom<SL2->SL2_|[SL2_!SL2.i: i in [1..#Generators(SL2)]]>;
        H:= H_ @@red;
        N:=Normalizer(GL2,H);
        N1,q1:=quo<N|H>;
            for S in AllSubgroups(N1) do;
                
                T:={};
                for t1 in Set(S) do;
                    
                    T:=T join {Integers(M)!(Determinant(t1@@q1))};
                end for;
                if (#T eq #U) and (IsAbelian(S) eq true) and (#S eq #U) then
                     
                     x:=#Generators(S);
                     y:=0;
                     for s in Generators(S) do;
                        
                        B1,B2:=Act(t,s@@q1,f,h); // t is the polynomial t here.
                        if IsWeaklyEqual(Evaluate(F!B1,R!SiegelExpansion(B2,prec)),Evaluate(F!f,R!SiegelExpansion(h,prec))) eq false then break;end if;
                        if IsWeaklyEqual(Evaluate(F!B1,R!SiegelExpansion(B2,prec)),Evaluate(F!f,R!SiegelExpansion(h,prec))) eq true then y:=y+1;end if;
                     end for;
                    if y eq x then G1:=S;break;end if;
                end if;
   
             end for;
        Gens :={};
        for g in G1 do;
            
            Gens:=Gens join {g@@q1};
        end for;
       
        Gens := Gens join Generators(H);
        G:=sub<GL2|[g:g in Gens]>;
        Gens:=Generators(G);
        Gamma`G:=G;
        Gamma`gens:=Gens;
        Gamma`index:=Index(GL2,G);
        Alllist[k][j]:=Gamma;
        
    end for;
   
end for; 

/* keys:=[k: k in Keys(VGlist)];
for k  in keys do
    subkeys:=[k1: k1 in Keys(Alllist[k])]; 
    for j in subkeys do;
    Gamma:=Alllist[k][j]; 
   
    N:=Gamma`N; G:=Gamma`G; 
    GL2:=GL(2,Integers(N));   

    Gamma`sup:=["1A"];
    for k2 in keys do
       subkeys1:=[k1: k1 in Keys(Alllist[k2])];  
        for k_ in subkeys1 do
        
        if k_ eq j and k2 eq k then continue k_; end if;
 
        Gamma_:=Alllist[k2][k_];
        N_:=Gamma_`N; G_:=Gamma_`G;

        if N mod N_ eq 0 then
           GL2_:=GL(2,Integers(N_));
           red:=hom<GL2->GL2_|[GL2_!GL2.i: i in [1..#Generators(GL2)]]>;
           for H in Subgroups(G_@@red) do;
           if IsConjugate(GL2,H`subgroup,G) then
              Gamma`sup:=Gamma`sup cat [Gamma_`label] cat ["N_"] cat ["k_"];
              break;
           end if;
           end for;
        end if;
    end for;
    end for;
    Alllist[k][j]:=Gamma;
end for;
end for;*/

keys:=[k: k in Keys(VGlist)];
level:=[VGlist[k]`N:k in keys];
ParallelSort(~level,~keys);
for k in keys do;
    
    subkeys:=[k1: k1 in Keys(Alllist[k])]; 
    for j in subkeys do;
        Write("Data.m",Alllist[k][j]);
    end for;
    Write("Data.m","............");
end for;

