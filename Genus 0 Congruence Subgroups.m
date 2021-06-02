// Magma code and data related to "A Classification of Genus 0 Modular curves with rational points",
// by Rakvi.


// list of all genus 0 congruence groups upto conjugation in PGL_2(Z)

CongSubgroup := recformat<N:RngIntElt, label:MonStgElt, gens:SeqEnum, index:RngIntElt, H:GrpMat, hauptmodul, h:RngSerPuisElt, J:FldFunRatUElt,sub :SeqEnum, sup :SeqEnum>;

/* Record for a congruence subgroup Gamma of genus 0.
   N:              level of Gamma
   label:          label of Gamma given by Cummin and Pauli (describes Gamma up to conjugacy in PGL_2(Z).
   H:              image of Gamma in SL_2(Z/NZ).
   gens:           generators for subgroup H of SL_2(Z/NZ).
   index:          index of Gamma in SL_2(Z).
                      the first cusp will be the one at infinity.
   hauptmodul:     An abstract description of a hauptmodul for Gamma.  It is in one of the following forms:
                   1) A sequence of records of type SiegelPower; represents the product of those Siegel powers.
                   2) A sequence of sequence as in (1); represents the sum of products of Siegel powers.

   h:              q-expansion for the hauptmodul.   
   J:              rational function such that J(h) is the modular j-invariant.
   
   sub:            is a congruence subgroup Gamma' contained in Gamma such that [Gamma:Gamma']= #Cusps(Gamma').
     Input given only for single cusp cases. This is nonempty for only those single cusp cases which are not listed in warning(2) below.

    sup:            in a list of congruence subgroups will give label of congruence subgroups Gamma' containing Gamma.

Warning(1) : Except 6J \subset 6A every other subgroup listed is normal and 6J is a subgroup of 6A upto conjugation.

Warning(2) : 11A,14A,15A,21A have no genus 0 congruence subgroup.
*/
   

            
/*
The following is a complete list of the congruence subgroups of genus 0 up to conjugacy in PGL_2(Z), indexed by their 
Cummin-Pauli name given. See http://www.uncg.edu/mat/faculty/pauli/congruence/congruence.html
*/

load "Hauptmodul and J(t).m";


CPlist:=AssociativeArray();     
CPlist["1A"]:= rec<CongSubgroup | N:=1,  label:="1A", gens:=[ ], index:=1>;

CPlist["2A"]:= rec<CongSubgroup | N:=2,  label:="2A", gens:=[ [1,1,1,0] ], index:=2, sub:=["2C"]>;
CPlist["2B"]:= rec<CongSubgroup | N:=2,  label:="2B", gens:=[ [0,1,1,0] ], index:=3>;
CPlist["2C"]:= rec<CongSubgroup | N:=2,  label:="2C", gens:=[ [1,0,0,1] ], index:=6>;

CPlist["3A"]:= rec<CongSubgroup | N:=3,  label:="3A", gens:=[ [ 0, 1, 2, 0 ] , [ 0, 2, 1, 0 ] , [ 1, 2, 2, 2 ] , [ 2, 0, 0, 2 ]  ], index:=3, sub:=["3C"]>;
CPlist["3B"]:= rec<CongSubgroup | N:=3,  label:="3B", gens:=[[ 0, 2, 1, 2 ] , [ 1, 2, 1, 0 ] , [ 2, 0, 0, 2 ] , [ 2, 1, 2, 0 ]  ], index:=4>;
CPlist["3C"]:= rec<CongSubgroup | N:=3,  label:="3C", gens:=[[ 2, 0, 0, 2 ] , [ 2, 1, 1, 1 ] ], index:=6>;
CPlist["3D"]:= rec<CongSubgroup | N:=3,  label:="3D", gens:=[[ 2, 0, 0, 2 ] ], index:=12>;

CPlist["4A"]:= rec<CongSubgroup | N:=4,  label:="4A", gens:=[[ 0, 1, 3, 0 ] , [ 1, 1, 1, 2 ] , [ 3, 0, 0, 3 ] ], index:=4,sub:=["4D"]>;
CPlist["4B"]:= rec<CongSubgroup | N:=4,  label:="4B", gens:=[[ 0, 1, 3, 2 ] , [ 1, 2, 2, 1 ] , [ 2, 1, 3, 0 ] , [ 3, 2, 2, 3 ] ], index:=6>;
CPlist["4C"]:= rec<CongSubgroup | N:=4,  label:="4C", gens:=[[ 0, 1, 3, 0 ] , [ 1, 2, 2, 1 ] , [ 2, 1, 3, 2 ] , [ 3, 2, 2, 3 ] ], index:=6>;
CPlist["4D"]:= rec<CongSubgroup | N:=4,  label:="4D", gens:=[[ 1, 1, 1, 2 ] , [ 3, 0, 0, 3 ] ], index:=8>;
CPlist["4E"]:= rec<CongSubgroup | N:=4,  label:="4E", gens:=[[ 1, 2, 2, 1 ] , [ 3, 2, 2, 3 ] ], index:=12>;
CPlist["4F"]:= rec<CongSubgroup | N:=4,  label:="4F", gens:=[[ 0, 1, 3, 0 ] , [ 3, 0, 0, 3 ] ], index:=12>;
CPlist["4G"]:= rec<CongSubgroup | N:=4,  label:="4G", gens:=[ [ 3, 0, 0, 3 ] ], index:=24>;

CPlist["5A"]:= rec<CongSubgroup | N:=5,  label:="5A", gens:=[[ 1, 1, 4, 0 ] , [ 2, 1, 0, 3 ] , [ 4, 0, 0, 4 ] , [ 4, 2, 4, 1 ] ], index:=5,sub:=["5E"]>;
CPlist["5B"]:= rec<CongSubgroup | N:=5,  label:="5B", gens:=[[ 2, 3, 3, 0 ] , [ 4, 0, 0, 4 ] , [ 4, 1, 3, 1 ] ], index:=6>;
CPlist["5C"]:= rec<CongSubgroup | N:=5,  label:="5C", gens:=[[ 3, 0, 1, 2 ] , [ 4, 0, 0, 4 ] , [ 4, 3, 3, 0 ] ], index:=10>;
CPlist["5D"]:= rec<CongSubgroup | N:=5,  label:="5D", gens:=[[ 2, 3, 3, 0 ] , [ 4, 0, 0, 4 ] ], index:=12>;
CPlist["5E"]:= rec<CongSubgroup | N:=5,  label:="5E", gens:=[[ 1, 3, 1, 4 ] , [ 3, 0, 3, 2 ] , [ 4, 0, 0, 4 ] ], index:=15>;
CPlist["5F"]:= rec<CongSubgroup | N:=5,  label:="5F", gens:=[ [4, 0, 0, 4 ] , [ 4, 3, 3, 0 ] ], index:=20>;
CPlist["5G"]:= rec<CongSubgroup | N:=5,  label:="5G", gens:=[ [ 2, 4, 0, 3 ] , [ 4, 0, 0, 4 ] ], index:=30>;
CPlist["5H"]:= rec<CongSubgroup | N:=5,  label:="5H", gens:=[[ 4, 0, 0, 4 ] ], index:=60>;

CPlist["6A"]:= rec<CongSubgroup | N:=6,  label:="6A", gens:=[[ 0, 1, 5, 1 ] , [ 1, 2, 2, 5 ] , [ 3, 4, 2, 3 ] , [ 5, 0, 0, 5 ] , [ 5, 3, 1, 2 ] , [ 5, 4, 4, 1 ] ], index:=6,sub:=["6J"]>;
CPlist["6B"]:= rec<CongSubgroup | N:=6,  label:="6B", gens:=[[ 2, 1, 1, 4 ] , [ 3, 2, 4, 3 ] , [ 4, 3, 3, 1 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 1, 1 ] ], index:=6,sub:=["6E"]>;
CPlist["6C"]:= rec<CongSubgroup | N:=6,  label:="6C", gens:=[[ 1, 3, 3, 4 ] , [ 3, 2, 4, 5 ] , [ 4, 3, 3, 1 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 2, 3 ] ], index:=8>;
CPlist["6D"]:= rec<CongSubgroup | N:=6,  label:="6D", gens:=[[ 3, 2, 4, 3 ] , [ 4, 3, 3, 4 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 1 ] ], index:=9>;
CPlist["6E"]:= rec<CongSubgroup | N:=6,  label:="6E", gens:=[[  1, 3, 3, 4 ] , [ 4, 3, 3, 1 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 1, 1 ] ], index:=12>;
CPlist["6F"]:= rec<CongSubgroup | N:=6,  label:="6F", gens:=[ [ 1, 0, 3, 1 ] , [ 3, 2, 4, 5 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 2, 3 ] , [ 5, 4, 5, 3 ] ], index:=12>;
CPlist["6G"]:= rec<CongSubgroup | N:=6,  label:="6G", gens:=[ [ 4, 3, 3, 4 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 1 ] ], index:=18>;
CPlist["6H"]:= rec<CongSubgroup | N:=6,  label:="6H", gens:=[ [0, 1, 5, 0 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 1 ]  ], index:=18>;
CPlist["6I"]:= rec<CongSubgroup | N:=6,  label:="6I", gens:=[[ 3, 2, 4, 5 ] , [ 3, 4, 2, 1 ] , [ 5, 4, 2, 3 ]] , index:=24>;
CPlist["6J"]:= rec<CongSubgroup | N:=6,  label:="6J", gens:=[[ 2, 1, 5, 3 ] , [ 5, 0, 0, 5 ] ] , index:=24>;
CPlist["6K"]:= rec<CongSubgroup | N:=6,  label:="6K", gens:=[[ 1, 0, 3, 1 ] , [ 5, 0, 0, 5 ] ] , index:=36>;
CPlist["6L"]:= rec<CongSubgroup | N:=6,  label:="6L", gens:=[[ 0, 1, 5, 0 ] , [ 0, 5, 1, 0 ] , [ 5, 0, 0, 5 ] ] , index:=36>;

CPlist["7A"]:= rec<CongSubgroup | N:=7,  label:="7A", gens:=[[ 0, 3, 2, 0 ] , [ 2, 5, 6, 5 ] , [ 4, 0, 6, 2 ] , [ 6, 0, 0, 6 ] , [ 6, 6, 2, 1 ] ], index:=7,sub:=["7C"]>;
CPlist["7B"]:= rec<CongSubgroup | N:=7,  label:="7B", gens:=[[ 3, 2, 0, 5 ] , [ 5, 3, 4, 4 ] , [ 6, 0, 0, 6 ] ], index:=8>;
CPlist["7C"]:= rec<CongSubgroup | N:=7,  label:="7C", gens:=[[ 1, 3, 4, 6 ] , [ 2, 0, 1, 4 ] , [ 2, 5, 6, 5 ] , [ 6, 0, 0, 6 ] ], index:=14>;
CPlist["7D"]:= rec<CongSubgroup | N:=7,  label:="7D", gens:=[[ 0, 3, 2, 0 ] , [ 1, 3, 4, 6 ] , [ 2, 5, 6, 5 ] , [ 6, 0, 0, 6 ] ], index:=21>;
CPlist["7E"]:= rec<CongSubgroup | N:=7,  label:="7E", gens:=[[ 6, 0, 0, 6 ] , [ 6, 2, 5, 3 ]  ], index:=24>;
CPlist["7F"]:= rec<CongSubgroup | N:=7,  label:="7F", gens:=[ [ 0, 3, 2, 0 ] , [ 4, 3, 5, 4 ] , [ 6, 0, 0, 6 ] ], index:=28>;
CPlist["7G"]:= rec<CongSubgroup | N:=7,  label:="7G", gens:=[ [ 0, 3, 2, 0 ] , [ 2, 5, 6, 5 ] , [ 6, 0, 0, 6 ] ], index:=42>;

CPlist["8A"]:= rec<CongSubgroup | N:=8,  label:="8A", gens:=[[ 1, 4, 4, 1 ] , [ 4, 1, 7, 0 ] , [ 4, 3, 5, 4 ] , [ 5, 0, 4, 5 ] , [ 5, 4, 0, 5 ] , [ 6, 3, 7, 1 ] , [ 7, 0, 0, 7 ] ], index:=8,sub:=["8E"]>;
CPlist["8B"]:= rec<CongSubgroup | N:=8,  label:="8B", gens:=[[ 0, 5, 3, 0 ] , [ 3, 6, 6, 7 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 5 ] , [ 7, 4, 4, 7 ] , [ 7, 6, 6, 3 ] ], index:=12>;
CPlist["8C"]:= rec<CongSubgroup | N:=8,  label:="8C", gens:=[[ 1, 4, 4, 1 ] , [ 3, 0, 0, 3 ] , [ 4, 5, 3, 2 ] , [ 5, 4, 4, 5 ] , [ 7, 2, 6, 3 ] ], index:=12>;
CPlist["8D"]:= rec<CongSubgroup | N:=8,  label:="8D", gens:=[[ 0, 5, 3, 0 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 5 ] , [ 7, 4, 4, 7 ] , [ 7, 6, 2, 3 ] ], index:=12>;
CPlist["8E"]:= rec<CongSubgroup | N:=8,  label:="8E", gens:=[[ 1, 1, 5, 6 ] , [ 1, 4, 4, 1 ] , [ 5, 0, 4, 5 ] , [ 6, 3, 7, 1 ] , [ 7, 0, 0, 7 ] ], index:=16>;
CPlist["8F"]:= rec<CongSubgroup | N:=8,  label:="8F", gens:=[ [ 0, 1, 7, 0 ] , [ 0, 3, 5, 0 ] , [ 2, 3, 3, 5 ] , [ 5, 0, 0, 5 ] , [ 7, 0, 0, 7 ] ], index:=16>;
CPlist["8G"]:= rec<CongSubgroup | N:=8,  label:="8G", gens:=[[ 1, 2, 0, 1 ] , [ 1, 4, 0, 1 ] , [ 1, 6, 0, 1 ] , [ 3, 2, 0, 3 ] , [ 5, 4, 0, 5 ]  ], index:=24>;
CPlist["8H"]:= rec<CongSubgroup | N:=8,  label:="8H", gens:=[[ 0, 5, 3, 0 ] , [ 1, 4, 4, 1 ] , [ 5, 0, 0, 5 ] , [ 7, 4, 4, 7 ] ], index:=24>;
CPlist["8I"]:= rec<CongSubgroup | N:=8,  label:="8I", gens:=[[ 3, 2, 6, 7 ] , [ 4, 5, 3, 2 ] , [ 5, 4, 4, 5 ] , [ 5, 6, 2, 1 ] ] , index:=24>;
CPlist["8J"]:= rec<CongSubgroup | N:=8,  label:="8J", gens:=[[ 1, 2, 4, 1 ] , [ 1, 4, 0, 1 ] , [ 1, 6, 4, 1 ] , [ 3, 2, 0, 3 ] , [ 5, 4, 4, 5 ] ] , index:=24>;
CPlist["8K"]:= rec<CongSubgroup | N:=8,  label:="8K", gens:=[[ 0, 5, 3, 0 ] , [ 1, 0, 4, 1 ] , [ 1, 4, 4, 1 ] , [ 7, 4, 4, 7 ] ] , index:=24>;
CPlist["8L"]:= rec<CongSubgroup | N:=8,  label:="8L", gens:=[[ 0, 7, 1, 0 ] , [ 3, 6, 6, 7 ] , [ 5, 4, 4, 5 ] , [ 7, 0, 0, 7 ] , [ 7, 2, 2, 3 ]  ] , index:=24>;
CPlist["8M"]:= rec<CongSubgroup | N:=8,  label:="8M", gens:=[ [ 0, 1, 7, 0 ] , [ 2, 3, 3, 5 ] , [ 7, 0, 0, 7 ] ] , index:=32>;
CPlist["8N"]:= rec<CongSubgroup | N:=8,  label:="8N", gens:=[ [ 1, 0, 4, 1 ] , [ 1, 4, 4, 1 ] , [ 7, 0, 0, 7 ] , [ 7, 4, 4, 7 ] ] , index:=48>;
CPlist["8O"]:= rec<CongSubgroup | N:=8,  label:="8O", gens:=[ [ 1, 4, 0, 1 ] , [ 5, 6, 0, 5 ] , [ 7, 4, 0, 7 ]  ] , index:=48>;
CPlist["8P"]:= rec<CongSubgroup | N:=8,  label:="8P", gens:=[ [ 0, 7, 1, 0 ] , [ 5, 4, 4, 5 ] , [ 7, 0, 0, 7 ] ] , index:=48>;

CPlist["9A"]:= rec<CongSubgroup | N:=9,  label:="9A", gens:=[[ 0, 1, 8, 0 ] , [ 1, 7, 1, 8 ] , [ 2, 6, 6, 5 ] , [ 7, 0, 0, 4 ] , [ 7, 6, 6, 4 ] ], index:=9,sub:=["9D"]>;
CPlist["9B"]:= rec<CongSubgroup | N:=9,  label:="9B", gens:=[[ 4, 0, 6, 7 ] , [ 7, 0, 6, 4 ] , [ 7, 0, 8, 4 ] , [ 8, 0, 0, 8 ] ], index:=12>;
CPlist["9C"]:= rec<CongSubgroup | N:=9,  label:="9C", gens:=[[ 1, 3, 2, 7 ] , [ 4, 0, 6, 7 ] , [ 7, 0, 6, 4 ] , [ 8, 0, 0, 8 ] ], index:=12>;
CPlist["9D"]:= rec<CongSubgroup | N:=9,  label:="9D", gens:=[[  0, 1, 8, 0 ] , [ 4, 6, 6, 7 ] , [ 5, 3, 3, 2 ] , [ 7, 0, 0, 4 ] ], index:=18>;
CPlist["9E"]:= rec<CongSubgroup | N:=9,  label:="9E", gens:=[[ 0, 1, 8, 0 ] , [ 4, 6, 3, 7 ] , [ 7, 0, 0, 4 ] , [ 8, 0, 0, 8 ] ], index:=18>;
CPlist["9F"]:= rec<CongSubgroup | N:=9,  label:="9F", gens:=[ [ 0, 1, 8, 0 ] , [ 0, 8, 1, 0 ] , [ 1, 3, 2, 7 ] , [ 4, 1, 1, 5 ] , [ 8, 0, 0, 8 ]  ], index:=27>;
CPlist["9G"]:= rec<CongSubgroup | N:=9,  label:="9G", gens:=[[ 0, 1, 8, 0 ] , [ 1, 7, 1, 8 ] , [ 4, 6, 6, 7 ] , [ 5, 3, 3, 2 ] ], index:=27>;
CPlist["9H"]:= rec<CongSubgroup | N:=9,  label:="9H", gens:=[[ 4, 0, 0, 7 ] , [ 4, 3, 6, 7 ] , [ 8, 0, 0, 8 ] ], index:=36>;
CPlist["9I"]:= rec<CongSubgroup | N:=9,  label:="9I", gens:=[[ 1, 0, 6, 1 ] , [ 7, 0, 5, 4 ] , [ 8, 0, 0, 8 ] ] , index:=36>;
CPlist["9J"]:= rec<CongSubgroup | N:=9,  label:="9J", gens:=[[ 1, 0, 6, 1 ] , [ 1, 3, 2, 7 ] , [ 8, 0, 0, 8 ] ] , index:=36>;
 
CPlist["10A"]:= rec<CongSubgroup | N:=10,  label:="10A", gens:=[[ 1, 4, 8, 3 ] , [ 1, 5, 5, 6 ] , [ 1, 8, 6, 9 ] , [ 3, 0, 8, 7 ] , [ 9, 0, 0, 9 ] ], index:=10,sub:=["10E"]>;
CPlist["10B"]:= rec<CongSubgroup | N:=10,  label:="10B", gens:=[[ 6, 5, 5, 1 ] , [ 7, 8, 8, 5 ] , [ 9, 0, 0, 9 ] , [ 9, 6, 3, 1 ] ], index:=12>;
CPlist["10C"]:= rec<CongSubgroup | N:=10,  label:="10C", gens:=[[ 1, 0, 5, 1 ] , [ 7, 8, 8, 5 ] , [ 9, 0, 0, 9 ] , [ 9, 6, 3, 1 ]  ], index:=18>;
CPlist["10D"]:= rec<CongSubgroup | N:=10,  label:="10D", gens:=[[ 1, 5, 5, 6 ] , [ 7, 4, 5, 3 ] , [ 9, 0, 0, 9 ] , [ 9, 8, 8, 5 ] ], index:=20>;
CPlist["10E"]:= rec<CongSubgroup | N:=10,  label:="10E", gens:=[[ 7, 6, 0, 3 ] , [ 8, 1, 7, 1 ] , [ 9, 0, 0, 9 ] , [ 9, 2, 4, 1 ] ], index:=30>;
CPlist["10F"]:= rec<CongSubgroup | N:=10,  label:="10F", gens:=[ [ 5, 2, 2, 7 ] , [ 5, 2, 7, 7 ] , [ 9, 0, 0, 9 ]  ], index:=36>;
CPlist["10G"]:= rec<CongSubgroup | N:=10,  label:="10G", gens:=[[ 1, 4, 7, 9 ] , [ 5, 2, 2, 7 ] , [ 9, 0, 0, 9 ] ], index:=36>;

//CPlist["11A"]:= rec<CongSubgroup | N:=11,  label:="11A", gens:=[[ 8, 2, 6, 3 ] , [ 9, 4, 2, 1 ] , [ 10, 0, 0, 10 ] ], index:=11>;

CPlist["12A"]:= rec<CongSubgroup | N:=12,  label:="12A", gens:=[[ 1, 4, 4, 5 ] , [ 1, 9, 9, 10 ] , [ 4, 9, 3, 4 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 1 ] , [ 7, 0, 0, 7 ] , [ 9, 8, 4, 9 ] ], index:=12,sub:=["12F"]>;
CPlist["12B"]:= rec<CongSubgroup | N:=12,  label:="12B", gens:=[[ 1, 6, 6, 1 ] , [ 3, 8, 10, 11 ] , [ 4, 3, 9, 7 ] , [ 7, 0, 6, 7 ] , [ 8, 1, 11, 3 ] , [ 9, 8, 4, 5 ] , [ 11, 0, 0, 11 ] ], index:=16>;
CPlist["12C"]:= rec<CongSubgroup | N:=12,  label:="12C", gens:=[[ 1, 4, 4, 5 ] , [ 1, 6, 6, 1 ] , [ 4, 3, 9, 4 ] , [ 5, 0, 0, 5 ] , [ 7, 0, 0, 7 ] , [ 7, 6, 6, 7 ] , [ 9, 4, 8, 9 ] ], index:=18>;
CPlist["12D"]:= rec<CongSubgroup | N:=12,  label:="12D", gens:=[[ 1, 6, 6, 1 ] , [ 4, 3, 9, 10 ] , [ 5, 0, 0, 5 ] , [ 5, 4, 4, 1 ] , [ 7, 0, 0, 7 ] , [ 7, 6, 6, 7 ] , [ 9, 4, 2, 9 ] , [ 10, 3, 9, 4 ] ], index:=18>;
CPlist["12E"]:= rec<CongSubgroup | N:=12,  label:="12E", gens:=[[ 1, 0, 6, 1 ] , [ 7, 0, 6, 7 ] , [ 9, 4, 8, 1 ] , [ 9, 8, 1, 5 ] , [ 9, 8, 4, 5 ] , [ 11, 4, 5, 3 ] , [ 11, 4, 8, 3 ] ], index:=24>;
CPlist["12F"]:= rec<CongSubgroup | N:=12,  label:="12F", gens:=[ [ 0, 1, 11, 0 ] , [ 5, 0, 0, 5 ] , [ 5, 8, 8, 1 ] , [ 7, 0, 0, 7 ] , [ 8, 1, 7, 4 ] , [ 10, 3, 3, 1 ] , [ 11, 0, 0, 11 ]  ], index:=24>;
CPlist["12G"]:= rec<CongSubgroup | N:=12,  label:="12G", gens:=[[ 1, 6, 6, 1 ] , [ 1, 10, 4, 5 ] , [ 4, 9, 3, 10 ] , [ 5, 0, 0, 5 ] , [ 5, 8, 2, 1 ] , [ 7, 0, 0, 7 ] ], index:=36>;
CPlist["12H"]:= rec<CongSubgroup | N:=12,  label:="12H", gens:=[[ 4, 1, 7, 8 ] , [ 1, 6, 6, 1 ] , [ 5, 0, 0, 5 ] , [ 9, 4, 8, 9 ] , [ 7, 6, 6, 7 ] , [ 4, 11, 5, 8 ] , [ 11, 0, 0, 11 ] , [ 3, 4, 8, 3 ]  ], index:=36>;
CPlist["12I"]:= rec<CongSubgroup | N:=12,  label:="12I", gens:=[[ 1, 6, 0, 1 ] , [ 3, 4, 8, 7 ] , [ 5, 4, 8, 9 ] , [ 7, 6, 6, 7 ] , [ 9, 8, 4, 5 ] ] , index:=48>;
CPlist["12J"]:= rec<CongSubgroup | N:=12,  label:="12J", gens:=[[ 3, 4, 8, 7 ] , [ 5, 4, 2, 9 ] , [ 5, 4, 5, 9 ] , [ 9, 8, 1, 5 ] , [ 9, 8, 4, 5 ] ] , index:=48>;

CPlist["13A"]:= rec<CongSubgroup | N:=13,  label:="13A", gens:=[[ 1, 3, 11, 8 ] , [ 7, 7, 4, 6 ] , [ 9, 2, 7, 6 ] , [ 12, 0, 0, 12 ] ], index:=14>;
CPlist["13B"]:= rec<CongSubgroup | N:=13,  label:="13B", gens:=[[ 0, 3, 4, 2 ] , [ 4, 0, 11, 10 ] , [ 5, 7, 3, 7 ]  ], index:=28>;
CPlist["13C"]:= rec<CongSubgroup | N:=13,  label:="13C", gens:=[[ 0, 3, 4, 2 ] , [ 6, 6, 9, 7 ] , [ 7, 2, 7, 4 ] ], index:=42>;

CPlist["14A"]:= rec<CongSubgroup | N:=14,  label:="14A", gens:=[[ 1, 9, 4, 9 ] , [ 5, 8, 2, 9 ] , [ 7, 12, 4, 7 ] , [ 8, 7, 7, 1 ] , [ 11, 12, 0, 9 ] , [ 13, 0, 0, 13 ] ], index:=14>;
CPlist["14B"]:= rec<CongSubgroup | N:=14,  label:="14B", gens:=[[ 1, 7, 7, 8 ] , [ 11, 8, 12, 5 ] , [ 13, 10, 2, 7 ] , [ 13, 12, 12, 9 ]  ], index:=16>;
CPlist["14C"]:= rec<CongSubgroup | N:=14,  label:="14C", gens:=[[  0, 1, 13, 13 ] , [ 3, 10, 8, 13 ] , [ 11, 8, 12, 5 ] , [ 13, 0, 0, 13 ]  ], index:=48>;

CPlist["15A"]:= rec<CongSubgroup | N:=15,  label:="15A", gens:=[[ 1, 3, 6, 4 ] , [ 1, 9, 8, 13 ] , [ 4, 0, 0, 4 ] , [ 6, 10, 5, 6 ] , [ 11, 0, 0, 11 ] , [ 11, 5, 5, 1 ] , [ 13, 0, 3, 7 ]  ], index:=15>;
CPlist["15B"]:= rec<CongSubgroup | N:=15,  label:="15B", gens:=[[ 6, 10, 5, 6 ] , [ 7, 3, 3, 10 ] , [ 11, 0, 0, 11 ] , [ 11, 5, 5, 1 ] , [ 14, 0, 0, 14 ] , [ 14, 1, 13, 1 ] ], index:=18>;
CPlist["15C"]:= rec<CongSubgroup | N:=15,  label:="15C", gens:=[[ 2, 10, 7, 13 ] , [ 6, 10, 5, 6 ] , [ 7, 3, 3, 10 ] , [ 11, 0, 0, 11 ] , [ 14, 0, 0, 14 ]  ], index:=36>;

CPlist["16A"]:= rec<CongSubgroup | N:=16,  label:="16A", gens:=[[ 1, 8, 8, 1 ] , [ 1, 9, 5, 14 ] , [ 1, 12, 4, 1 ] , [ 4, 5, 3, 4 ] , [ 9, 0, 8, 9 ] , [ 13, 0, 12, 5 ] , [ 14, 11, 7, 1 ] , [ 15, 8, 8, 15 ] ], index:=16,sub:=["16F"]>;
CPlist["16B"]:= rec<CongSubgroup | N:=16,  label:="16B", gens:=[[ 1, 8, 8, 1 ] , [ 1, 10, 10, 5 ] , [ 2, 7, 13, 14 ] , [ 5, 4, 4, 13 ] , [ 9, 0, 0, 9 ] , [ 9, 8, 8, 9 ] , [ 11, 6, 6, 15 ] , [ 15, 0, 0, 15 ] , [ 15, 12, 12, 15 ] ], index:=24>;
CPlist["16C"]:= rec<CongSubgroup | N:=16,  label:="16C", gens:=[[ 1, 8, 8, 1 ] , [ 1, 12, 12, 1 ] , [ 5, 4, 12, 13 ] , [ 6, 1, 7, 12 ] , [ 9, 0, 0, 9 ] , [ 9, 8, 8, 9 ] , [ 11, 2, 14, 7 ] , [ 13, 2, 6, 1 ] ], index:=24>;
CPlist["16D"]:= rec<CongSubgroup | N:=16,  label:="16D", gens:=[[ 1, 8, 8, 1 ] , [ 1, 12, 4, 1 ] , [ 2, 9, 7, 0 ] , [ 5, 4, 12, 13 ] , [ 9, 0, 0, 9 ] , [ 9, 8, 8, 9 ] , [ 11, 2, 14, 7 ] , [ 13, 2, 14, 1 ] ], index:=24>;
CPlist["16E"]:= rec<CongSubgroup | N:=16,  label:="16E", gens:=[[ 1, 8, 8, 1 ] , [ 4, 3, 5, 4 ] , [ 9, 0, 0, 9 ] , [ 11, 6, 10, 7 ] , [ 13, 8, 8, 5 ] , [ 13, 12, 4, 5 ] , [ 15, 8, 8, 15 ] ], index:=24>;
CPlist["16F"]:= rec<CongSubgroup | N:=16,  label:="16F", gens:=[ [ 1, 8, 8, 1 ] , [ 7, 0, 8, 7 ] , [ 9, 0, 8, 9 ] , [ 9, 1, 5, 6 ] , [ 9, 4, 4, 9 ] , [ 13, 0, 12, 5 ] , [ 13, 8, 4, 5 ] , [ 15, 8, 8, 15 ]  ], index:=32>;
CPlist["16G"]:= rec<CongSubgroup | N:=16,  label:="16G", gens:=[[ 1, 4, 0, 1 ] , [ 1, 6, 0, 1 ] , [ 1, 8, 0, 1 ] , [ 3, 12, 8, 11 ] , [ 9, 0, 0, 9 ] , [ 9, 8, 0, 9 ] , [ 13, 0, 8, 5 ]  ], index:=48>;
CPlist["16H"]:= rec<CongSubgroup | N:=16,  label:="16H", gens:=[[ 1, 8, 8, 1 ] , [ 2, 1, 15, 0 ] , [ 9, 8, 8, 9 ] , [ 13, 4, 12, 5 ] , [ 13, 6, 10, 1 ] , [ 13, 12, 4, 5 ] , [ 15, 6, 10, 3 ] ], index:=48>;


CPlist["18A"]:= rec<CongSubgroup | N:=18,  label:="18A", gens:=[[ 1, 9, 9, 10 ] , [ 5, 12, 12, 11 ] , [ 7, 0, 0, 13 ] , [ 9, 10, 17, 9 ] , [ 11, 10, 1, 1 ] , [ 13, 6, 6, 7 ] ], index:=18,sub:=["18D"]>;
CPlist["18B"]:= rec<CongSubgroup | N:=18,  label:="18B", gens:=[[ 1, 0, 6, 1 ] , [ 1, 9, 9, 10 ] , [ 1, 12, 2, 7 ] , [ 13, 0, 12, 7 ] , [ 17, 0, 0, 17 ]
 ], index:=24>;
CPlist["18C"]:= rec<CongSubgroup | N:=18,  label:="18C", gens:=[[ 1, 0, 6, 1 ] , [ 1, 0, 10, 1 ] , [ 7, 15, 3, 4 ] , [ 13, 0, 12, 7 ] , [ 17, 0, 0, 17 ] ], index:=24>;
CPlist["18D"]:= rec<CongSubgroup | N:=18,  label:="18D", gens:=[[ 5, 12, 12, 11 ] , [ 7, 0, 0, 13 ] , [ 7, 12, 12, 13 ] , [ 9, 10, 17, 9 ] , [ 10, 9, 9, 1 ] ], index:=36>;
CPlist["18E"]:= rec<CongSubgroup | N:=18,  label:="18E", gens:=[[ 1, 0, 6, 1 ] , [ 1, 0, 9, 1 ] , [ 1, 0, 12, 1 ] , [ 7, 0, 14, 13 ] , [ 13, 0, 0, 7 ] , [ 17, 0, 0, 17 ]  ], index:=36>;

CPlist["20A"]:= rec<CongSubgroup | N:=20,  label:="20A", gens:=[[  1, 0, 10, 1 ] , [ 5, 12, 12, 17 ] , [ 5, 12, 17, 17 ] , [ 9, 0, 0, 9 ] , [ 11, 0, 10, 11 ] , [ 11, 14, 17, 9 ]  ], index:=36>;

CPlist["21A"]:= rec<CongSubgroup | N:=21,  label:="21A", gens:=[[ 1, 7, 7, 8 ] , [ 1, 18, 3, 13 ] , [ 6, 17, 4, 15 ] , [ 7, 3, 9, 7 ] , [ 7, 15, 6, 13 ] , [ 8, 0, 0, 8 ] , [ 10, 15, 18, 4 ] , [ 13, 0, 0, 13 ] , [ 15, 7, 14, 15 ]   ], index:=21>;

CPlist["24A"]:= rec<CongSubgroup | N:=24,  label:="24A", gens:=[[ 1, 0, 12, 1 ] , [ 1, 8, 20, 17 ] , [ 1, 16, 4, 17 ] , [ 7, 0, 0, 7 ] , [ 13, 0, 12, 13 ] , [ 13, 12, 6, 13 ] , [ 13, 12, 18, 13 ] , [ 17, 0, 0, 17 ] , [ 19, 0, 12, 19 ] , [ 19, 18, 3, 13 ] ], index:=36>;
CPlist["24B"]:= rec<CongSubgroup | N:=24,  label:="24B", gens:=[[  1, 0, 12, 1 ] , [ 1, 0, 18, 1 ] , [ 1, 8, 0, 1 ] , [ 7, 12, 6, 7 ] , [ 11, 0, 21, 11 ] , [ 13, 0, 0, 13 ] , [ 13, 0, 12, 13 ] , [ 19, 12, 15, 7 ] , [ 23, 0, 0, 23 ]  ], index:=48>;

CPlist["25A"]:= rec<CongSubgroup | N:=25,  label:="25A", gens:=[[ 6, 10, 20, 21 ] , [ 8, 21, 6, 19 ] , [ 9, 11, 18, 11 ] , [ 11, 0, 10, 16 ] , [ 24, 0, 0, 24 ]  ], index:=30>;
CPlist["25B"]:= rec<CongSubgroup | N:=25,  label:="25B", gens:=[[ 6, 0, 5, 21 ] , [ 6, 15, 15, 21 ] , [ 7, 23, 18, 20 ] , [ 16, 0, 15, 11 ] , [ 19, 0, 20, 4 ]  ], index:=60>;

CPlist["26A"]:= rec<CongSubgroup | N:=26,  label:="26A", gens:=[[ 5, 20, 16, 7 ] , [ 11, 14, 3, 11 ] , [ 13, 16, 4, 15 ] , [ 14, 13, 13, 1 ] , [ 17, 0, 24, 23 ]  ], index:=28>;

CPlist["27A"]:= rec<CongSubgroup | N:=27,  label:="27A", gens:=[[ 1, 0, 18, 1 ] , [ 10, 0, 0, 19 ] , [ 10, 0, 24, 19 ] , [ 13, 9, 1, 7 ] , [ 16, 18, 25, 13 ] , [ 26, 0, 0, 26 ]  ], index:=36>;

CPlist["28A"]:= rec<CongSubgroup | N:=28,  label:="28A", gens:=[[ 1, 14, 14, 1 ] , [ 13, 14, 0, 13 ] , [ 13, 20, 8, 21 ] , [ 15, 14, 0, 15 ] , [ 17, 24, 8, 13 ] , [ 22, 21, 21, 1 ] , [ 25, 8, 12, 5 ]  ], index:=32>;

CPlist["30A"]:= rec<CongSubgroup | N:=30,  label:="30A", gens:=[[ 1, 10, 10, 11 ] , [ 7, 18, 18, 25 ] , [ 11, 0, 0, 11 ] , [ 16, 15, 15, 1 ] , [ 21, 10, 20, 21 ] , [ 27, 25, 2, 3 ] , [ 29, 0, 0, 29 ]  ], index:=36>;

CPlist["32A"]:= rec<CongSubgroup | N:=32,  label:="32A", gens:=[[ 1, 16, 16, 1 ] , [ 1, 28, 28, 17 ] , [ 5, 20, 12, 29 ] , [ 9, 8, 24, 25 ] , [ 9, 24, 8, 25 ] , [ 11, 26, 6, 23 ] , [ 13, 4, 12, 21 ] , [ 17, 10, 6, 13 ] , [ 17, 16, 16, 17 ] , [ 19, 26, 22, 15 ] , [ 23, 10, 30, 27 ] , [ 26, 29, 27, 8 ]  ], index:=48>;

CPlist["36A"]:= rec<CongSubgroup | N:=36,  label:="36A", gens:=[[ 1, 0, 24, 1 ] , [ 1, 18, 18, 1 ] , [ 10, 27, 27, 1 ] , [ 19, 18, 0, 19 ] , [ 25, 0, 24, 13 ] , [ 25, 24, 16, 1 ] , [ 35, 0, 0, 35 ] ], index:=48>;

CPlist["48A"]:= rec<CongSubgroup | N:=48,  label:="48A", gens:=[[ 1, 0, 24, 1 ] , [ 3, 10, 47, 45 ] , [ 17, 0, 0, 17 ] , [ 17, 32, 32, 1 ] , [ 23, 0, 24, 23 ] , [ 25, 0, 24, 25 ] , [ 25, 20, 14, 17 ] , [ 33, 32, 16, 33 ] , [ 37, 0, 36, 13 ] , [ 41, 24, 36, 41 ]  ], index:=72>;



// Computing Hauptmodul for multiple cusp cases except 10E, 12F, 12H.
for k in Keys(CPlist) do
	if k eq "1A" or k eq "2A" or k eq "3A" or k eq "4A" or k eq "5A" or k eq "6A" or k eq "6B" or k eq "7A" or k eq "8A" or k eq "9A" or k eq "10A" or k eq "10E" or k eq "12F" or k eq "11A" or k eq "12A" or k eq "14A" or k eq "15A" or k eq "16A" or k eq "18A" or k eq "21A" then 
        continue k;
    end if;
	Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
	Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    H_:= sub<SL2|[[1,0,0,1]]>; // This is just a dummy variable in multiple cusp case.
	ind := Gamma`index;
 	Gamma`hauptmodul:=FindHauptmodul(Gamma`H,H_);
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
     
    Gamma`h := R!SiegelExpansion(h1,10); 
    
  
    
    
    CPlist[k] :=Gamma;

end for;


//Computing Hauptmodul for rest of the cases.


for k in Keys(CPlist) do
	

     if k eq "2A" or k eq "3A" or k eq "4A" or k eq "5A" or k eq "6B" or k eq "7A" or k eq "8A" or k eq "9A" or k eq "16A" or k eq "18A" then 
        
	Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
	Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    Gamma_:= CPlist[Gamma`sub[1]];
    H_:= Gamma_`H; 
	ind := Gamma`index;
 	Gamma`hauptmodul:=FindHauptmodul(Gamma`H,H_);
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;

	
    if k eq "6A" then
    
    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
	Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    H_ := sub<SL2|[[0,1,5,1],[5,0,0,5]]>;
    ind := Gamma`index;
 	Gamma`hauptmodul:=FindHauptmodul(Gamma`H,H_);
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul;
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    
    CPlist[k] :=Gamma;
    end if;

    if k eq "14A" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z14> := CyclotomicField(N); 

    L<z84> := CyclotomicField(84); 

	Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0 := [rec<SiegelPower | a := [ 0, 2/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 2/14, 8/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 2/14, 12/14 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 4/14, 0], m := 1, c := K!1>, rec<SiegelPower | a := [ 4/14, 6/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 4/14, 12/14 ], m := 1, c := K!1/(-z84^12 + z84^6 + 1)> ]; 

    t1 := [rec<SiegelPower | a := [ 0, 4/14 ], m := 1, c := K!(z84^22 - z84^18 - z84^16 + z84^12 - z84^8 - z84^6 + z84^2 + 1)>, rec<SiegelPower | a := [ 2/14, 2/14 ], m := 1, c := K!1/(-z84^12 + z84^6 + 1)>, 

            rec<SiegelPower | a := [ 2/14, 4/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 2/14, 6/14], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/14, 2/14 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/14, 8/14 ], m := 1, c := K!1> ]; 

    t2 := [rec<SiegelPower | a := [ 0, 6/14 ], m := 1, c := K!(z84^6/(-z84^12 + z84^6 + 1))>, rec<SiegelPower | a := [ 4/14, 8/14 ], m := 1, c := K!1>, 
           rec<SiegelPower | a := [ 4/14, 10/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/14, 0/14], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/14, 6/14 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/14, 10/14 ], m := 1, c := K!1> ]; 

    t3 := [ rec<SiegelPower | a := [ 2/14, 0/14 ], m := 1, c := K!(z84^22-z84^8)>, rec<SiegelPower | a := [ 2/14, 10/14 ], m := 1, c := K!1/(-z84^12 + z84^6 + 1)>, 
            rec<SiegelPower | a := [ 4/14, 2/14 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 4/14, 4/14], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/14, 4/14 ], m := 1, c := K!1>, 

        rec<SiegelPower | a := [ 6/14, 12/14 ], m := 1, c := K!1> ]; 

    t := [t0,t1,t2,t3];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;

    if k eq "15A" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z15> := CyclotomicField(N); 
    L<z60> := CyclotomicField(60); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0 := [ rec<SiegelPower | a := [ 0, 3/15 ], m := 1, c := K!(1/(-z60^12 + 2*z60^2))>, rec<SiegelPower | a := [ 0/15, 6/15 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 3/15, 12/15 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/15, 9/15], m := 1, c := K!1> ]; 

    t1 := [ rec<SiegelPower | a := [ 3/15, 6/15 ], m := 1, c := K!(-z60^8/(-z60^12 + 2*z60^2))>, rec<SiegelPower | a := [ 3/15, 3/15 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/15, 12/15 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/15, 6/15], m := 1, c := K!1> ]; 

    t2 := [ rec<SiegelPower | a := [ 3/15, 9/15 ], m := 1, c := K!(z60^10/(-z60^12 + 2*z60^2))>, rec<SiegelPower | a := [ 3/15, 0/15 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/15, 0/15 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/15, 3/15], m := 1, c := K!1> ]; 
    t := [t0,t1,t2];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;

    if k eq "21A" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z21> := CyclotomicField(N); 
    L<z84> := CyclotomicField(84); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0 := [ rec<SiegelPower | a := [ 0, 3/21 ], m := 1, c := K!(-1/(-z21^11 - 2*z21^6 - z21^4 + z21^3) )>, rec<SiegelPower | a := [ 3/21, 15/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/21, 15/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/21, 18/21], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/21, 0/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/21, 3/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 9/21, 18/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 9/21, 9/21], m := 1, c := K!1> ]; 

    t1 := [ rec<SiegelPower | a := [ 0/21, 6/21 ], m := 1, c := K!(1/(-z21^11 - 2*z21^6 - z21^4 + z21^3) )>, rec<SiegelPower | a := [ 3/21, 18/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 3/21, 3/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 3/21, 9/21], m := 1, c := K!1>, rec<SiegelPower | a := [ 3/21, 12/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/21, 9/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 6/21, 12/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 9/21, 0/21], m := 1, c := K!1> ]; 

    t2 := [ rec<SiegelPower | a := [ 0/21, 9/21 ], m := 1, c := K!((z84^22 - z84^18 - z84^16 + z84^12 - z84^8 - z84^6 + z84^2 + 1)/(-z21^11 - 2*z21^6 - z21^4 + z21^3) ) >, rec<SiegelPower | a := [ 3/21, 0/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 3/21, 6/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 6/21, 6/21], m := 1, c := K!1>, rec<SiegelPower | a := [ 9/21, 12/21 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 9/21, 15/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 9/21, 3/21 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 9/21, 6/21], m := 1, c := K!1> ]; 

     t := [t0,t1,t2];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;
    

    if k eq "10E" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z10> := CyclotomicField(N); 
    L<z60> := CyclotomicField(60); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0 := [ rec<SiegelPower | a := [ 1/10, 4/10 ], m := 1, c := L!(1/(-3*z60^15 + 3*z60^11 + 3*z60^9 - 3*z60^3 - 3*z60))>, rec<SiegelPower | a := [ 5/10, 2/10 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 5/10, 4/10 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 3/10, 2/10], m := 1, c := K!1>, rec<SiegelPower | a := [ 1/10, 3/10 ], m := -1, c := K!1>, 

            rec<SiegelPower | a := [ 3/10, 9/10 ], m := -1, c := K!1>, rec<SiegelPower | a := [ 1/10, 5/10 ], m := -1, c := K!1>, rec<SiegelPower | a := [ 3/10, 5/10], m := -1, c := K!1> ]; 

    t1 := [ rec<SiegelPower | a := [ 1/10, 7/10 ], m := 1, c := L!((z60^14 + z60^12 - z60^6 - z60^4 + 1)/(-3*z60^15 + 3*z60^11 + 3*z60^9 - 3*z60^3 - 3*z60))>, rec<SiegelPower | a := [ 1/10, 1/10 ], m := 1, 
            c := K!1>, rec<SiegelPower | a := [ 3/10, 1/10 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 3/10, 3/10], m := 1, c := K!1>, rec<SiegelPower | a := [ 0/10, 1/10 ], m := -1,  c := K!1>, 

            rec<SiegelPower | a := [ 2/10, 3/10 ], m := -1, c := K!1>, rec<SiegelPower | a := [ 4/10, 1/10 ], m := -1,  c := K!1>, rec<SiegelPower | a := [ 0/10, 3/10], m := -1, c := K!1> ]; 

    t2 := [ rec<SiegelPower | a := [ 2/10, 5/10 ], m := 1, c := L!((z60^12)/(-3*z60^15 + 3*z60^11 + 3*z60^9 - 3*z60^3 - 3*z60))>, rec<SiegelPower | a := [ 4/10, 5/10 ], m := 1, c := K!1>, 

            rec<SiegelPower | a := [ 2/10, 1/10 ], m := 1, c := K!1>, rec<SiegelPower | a := [ 4/10, 7/10], m := 1, c := K!1>, rec<SiegelPower |  a := [ 1/10, 2/10 ], m := -1, c := K!1>, 

            rec<SiegelPower |a := [ 1/10, 6/10 ], m := -1, c := K!1>, rec<SiegelPower | a := [ 3/10, 6/10 ], m := -1,  c := K!1>, rec<SiegelPower | a := [ 3/10, 8/10], m := -1, c := K!1> ];     

    t3 := [ rec<SiegelPower | a := [ 2/10, 5/10 ], m := 0, c := K!(-(z10^2 - z10))>];

     t := [t0,t1,t2,t3];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    

    end if;

    if k eq "12F" then
    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z12> := CyclotomicField(N);
    L<z24> := CyclotomicField(24); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0 := [ 

    rec<SiegelPower | 

        a := [ 3/12, 11/12 ], 

        m := 1, 

        c := L!(1/(2*z24))>, 

    rec<SiegelPower | 

        a := [ 3/12, 8/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 6/12, 5/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 6/12, 1/12], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 3/12, 7/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 3/12, 4/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 1/12, 8/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 1/12, 5/12], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 5/12, 4/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 5/12, 1/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 2/12, 1/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 2/12, 7/12], 

        m := 1, 

        c := K!1> 

]; 

t1 := [ 

    rec<SiegelPower | 

        a := [ 5/12, 2/12 ], 

        m := 1, 

        c := L!(z24^3/(2*z24))>, 

    rec<SiegelPower | 

        a := [ 1/12, 3/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 1/12, 6/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 5/12, 11/12], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 4/12, 3/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 4/12, 7/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 4/12, 9/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 4/12, 1/12], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 5/12, 3/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 5/12, 6/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 1/12, 7/12 ], 

        m := 1, 

        c := K!1>, 

    rec<SiegelPower | 

        a := [ 1/12, 10/12], 

        m := 1, 

        c := K!1> 

]; 

t2 := [ 

    rec<SiegelPower | 

        a := [ 5/12, 2/12 ], 

        m := 0, 

        c := K!(-(- z12^3 + z12^2 + z12) )>];

    t := [t0,t1,t2];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;

    end for;
 
for k in Keys(CPlist) do

    if k eq "10A" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z10> := CyclotomicField(N); 
    L<z60> := CyclotomicField(60); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0:=[rec<SiegelPower | a := [ 1/10, 2/5 ],m := 1,c := L!-1/3*z60^3>,rec<SiegelPower | a := [ 1/2, 1/5 ],m := 1,c := L!1>,rec<SiegelPower | a := [ 1/2, 2/5 ],m := 1,c := L!1>,
         rec<SiegelPower | a := [ 3/10, 1/5 ],m := 1,c := L!1>,rec<SiegelPower | a := [ 1/10, 3/10 ],m := -1,c := L!1>,rec<SiegelPower | a := [ 3/10, 9/10 ],m := -1,c := L!1>,
         rec<SiegelPower | a := [ 1/10, 1/2 ],m := -1,c := L!1>,rec<SiegelPower | a := [ 3/10, 1/2 ],m := -1,c := L!1>];
    t1 :=[
            rec<SiegelPower | 
                a := [ 1/10, 7/10 ],
                m := 1,
                c := L!1/3*(-z60^11 + z60)>,
            rec<SiegelPower | 
                a := [ 1/10, 1/10 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 3/10, 1/10 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 3/10, 3/10 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 0, 1/10 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/5, 3/10 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 2/5, 1/10 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 0, 3/10 ],
                m := -1,
                c := L!1>
        ];
    t2:=[
            rec<SiegelPower | 
                a := [ 1/5, 1/2 ],
                m := 1,
                c := L!-1/3*z60^15>,
            rec<SiegelPower | 
                a := [ 2/5, 1/2 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/5, 1/10 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 2/5, 7/10 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/10, 1/5 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/10, 3/5 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 3/10, 3/5 ],
                m := -1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 3/10, 4/5 ],
                m := -1,
                c := L!1>
        ];
    t3:=[
            rec<SiegelPower | 
                a := [ 1/5, 1/2 ],
                m := 0,
                c := L!-z60^12 + z60^6>
        ];
    t4:=[
            rec<SiegelPower | 
                a := [ 3/10, 9/10 ],
                m := 1,
                c := L!-1/3*z60^4>,
            rec<SiegelPower | 
                a := [ 3/10, 1/2 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 1/10, 1/2 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 1/10, 3/10 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 1/5, 9/10 ],
                m := -1,
                c := L!z60^14 - z60^10 - z60^8 + z60^2 + 1>,
            rec<SiegelPower | 
                a := [ 2/5, 3/10 ],
                m := -1,
                c := L!z60^11>,
            rec<SiegelPower | 
                a := [ 2/5, 9/10 ],
                m := -1,
                c := L!z60^2>,
            rec<SiegelPower | 
                a := [ 1/5, 7/10 ],
                m := -1,
                c := L!z60^14 - z60^10 - z60^8 + z60^2 + 1>
        ];
    t5:=[
            rec<SiegelPower | 
                a := [ 2/5, 1/10 ],
                m := 1,
                c := L!-1/3*z60^4>,
            rec<SiegelPower | 
                a := [ 0, 1/10 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 1/5, 3/10 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 0, 3/10 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 1/10, 0 ],
                m := -1,
                c := L!z60^10 - 1>,
            rec<SiegelPower | 
                a := [ 1/10, 4/5 ],
                m := -1,
                c := L!-z60^13 + z60^3>,
            rec<SiegelPower | 
                a := [ 3/10, 2/5 ],
                m := -1,
                c := L!-z60^10 + 1>,
            rec<SiegelPower | 
                a := [ 3/10, 0 ],
                m := -1,
                c := L!z60^10 - 1>
        ];
    t6:=[
            rec<SiegelPower | 
                a := [ 3/10, 4/5 ],
                m := 1,
                c := L!1/3*(z60^14 - z60^10 - z60^8 - z60^6 + z60^2 + 1)>,
            rec<SiegelPower | 
                a := [ 1/10, 3/5 ],
                m := 1,
                c := L!z60^7>,
            rec<SiegelPower | 
                a := [ 1/10, 1/5 ],
                m := 1,
                c := L!z60^10>,
            rec<SiegelPower | 
                a := [ 3/10, 3/5 ],
                m := 1,
                c := L!z60>,
            rec<SiegelPower | 
                a := [ 1/10, 9/10 ],
                m := -1,
                c := L!-z60^13 + z60^3>,
            rec<SiegelPower | 
                a := [ 1/2, 1/10 ],
                m := -1,
                c := L!-z60^15 + z60^11 + z60^9 + z60^7 - z60^3 - z60>,
            rec<SiegelPower | 
                a := [ 3/10, 7/10 ],
                m := -1,
                c := L!-z60^15 - z60^13 + z60^9 + z60^7 + z60^5 - z60>,
            rec<SiegelPower | 
                a := [ 1/2, 3/10 ],
                m := -1,
                c := L!z60^11>
        ];
    t7:=[
            rec<SiegelPower | 
                a := [ 3/10, 4/5 ],
                m := 0,
                c := L!-z60^12 + z60^6>
        ];
    t8:=[
            rec<SiegelPower | 
                a := [ 2/5, 3/10 ],
                m := 1,
                c := L!-1/3*z60^15>,
            rec<SiegelPower | 
                a := [ 1/5, 7/10 ],
                m := 1,
                c := L!z60^12>,
            rec<SiegelPower | 
                a := [ 2/5, 9/10 ],
                m := 1,
                c := L!-1>,
            rec<SiegelPower | 
                a := [ 1/5, 9/10 ],
                m := 1,
                c := L!z60^12>,
            rec<SiegelPower | 
                a := [ 3/10, 1/5 ],
                m := -1,
                c := L!z60^15 - z60^11 - z60^9 + z60^3 + z60>,
            rec<SiegelPower | 
                a := [ 1/10, 2/5 ],
                m := -1,
                c := L!z60^14 - z60^4>,
            rec<SiegelPower | 
                a := [ 1/2, 2/5 ],
                m := -1,
                c := L!-z60^15>,
            rec<SiegelPower | 
                a := [ 1/2, 1/5 ],
                m := -1,
                c := L!-z60^15>
        ];
    t9:=[
            rec<SiegelPower | 
                a := [ 3/10, 2/5 ],
                m := 1,
                c := L!1/3*(z60^15 - z60^11 - z60^9 + z60^3 + z60)>,
            rec<SiegelPower | 
                a := [ 1/10, 0 ],
                m := 1,
                c := L!-z60^15 + z60^11 + z60^9 - z60^3 - z60>,
            rec<SiegelPower | 
                a := [ 1/10, 4/5 ],
                m := 1,
                c := L!-z60^14 + z60^4>,
            rec<SiegelPower | 
                a := [ 3/10, 0 ],
                m := 1,
                c := L!z60^3>,
            rec<SiegelPower | 
                a := [ 1/10, 1/10 ],
                m := -1,
                c := L!-z60^3>,
            rec<SiegelPower | 
                a := [ 3/10, 1/10 ],
                m := -1,
                c := L!z60^15 - z60^11 - z60^9 + z60^3 + z60>,
            rec<SiegelPower | 
                a := [ 1/10, 7/10 ],
                m := -1,
                c := L!z60^6>,
            rec<SiegelPower | 
                a := [ 3/10, 3/10 ],
                m := -1,
                c := L!z60^15 - z60^11 - z60^9 + z60^3 + z60>
        ];
    t10:=[
            rec<SiegelPower | 
                a := [ 1/2, 3/10 ],
                m := 1,
                c := L!1/3>,
            rec<SiegelPower | 
                a := [ 1/2, 1/10 ],
                m := 1,
                c := L!z60^15>,
            rec<SiegelPower | 
                a := [ 1/10, 9/10 ],
                m := 1,
                c := L!-z60^14 + z60^4>,
            rec<SiegelPower | 
                a := [ 3/10, 7/10 ],
                m := 1,
                c := L!z60^15>,
            rec<SiegelPower | 
                a := [ 1/5, 1/10 ],
                m := -1,
                c := L!z60^12>,
            rec<SiegelPower | 
                a := [ 2/5, 1/2 ],
                m := -1,
                c := L!-z60^15>,
            rec<SiegelPower | 
                a := [ 2/5, 7/10 ],
                m := -1,
                c := L!-z60^9>,
            rec<SiegelPower | 
                a := [ 1/5, 1/2 ],
                m := -1,
                c := L!z60^3>
        ];
    t11:=[
            rec<SiegelPower | 
                a := [ 1/2, 3/10 ],
                m := 0,
                c := L!-z60^12 + z60^6>
        ];
        
        
    t := [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    end if;

    if k eq "12A" then

    Gamma:=CPlist[k];	
	N:=Gamma`N;
	SL2:=SL(2,Integers(N));
    K<z12> := CyclotomicField(N); 
    L<z24> := CyclotomicField(24); 
    Gamma`H:=sub< SL2 | Gamma`gens cat [[-1,0,0,-1]]>;
    t0:=[
            rec<SiegelPower | 
                a := [ 1/4, 11/12 ],
                m := 1,
                c := L!1/2*(-z24^7 + z24^3)>,
            rec<SiegelPower | 
                a := [ 1/4, 2/3 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/2, 5/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/2, 1/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/4, 7/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/4, 1/3 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/12, 2/3 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/12, 5/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 1/3 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 1/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/6, 1/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/6, 7/12 ],
                m := 1,
                c := L!1>
        ];
    t1 :=[
            rec<SiegelPower | 
                a := [ 5/12, 1/6 ],
                m := 1,
                c := L!1/2*z24^2>,
            rec<SiegelPower | 
                a := [ 1/12, 1/4 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/12, 1/2 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 11/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/3, 1/4 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/3, 7/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/3, 3/4 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/3, 1/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 1/4 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 1/2 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/12, 7/12 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/12, 5/6 ],
                m := 1,
                c := L!1>
        ];
    t2:=[
            rec<SiegelPower | 
                a := [ 5/12, 1/6 ],
                m := 0,
                c := L!z12^3 - z12^2 - z12>
        ];
    t3:=[
            rec<SiegelPower | 
                a := [ 1/4, 5/6 ],
                m := 1,
                c := L!1/2*(-z24^4 + 1)>,
            rec<SiegelPower | 
                a := [ 1/4, 5/12 ],
                m := 1,
                c := L!z24>,
            rec<SiegelPower | 
                a := [ 0, 5/12 ],
                m := 1,
                c := L!-z24^3>,
            rec<SiegelPower | 
                a := [ 0, 1/12 ],
                m := 1,
                c := L!z24^5>,
            rec<SiegelPower | 
                a := [ 1/4, 1/6 ],
                m := 1,
                c := L!z24^2>,
            rec<SiegelPower | 
                a := [ 1/4, 1/12 ],
                m := 1,
                c := L!z24>,
            rec<SiegelPower | 
                a := [ 1/12, 11/12 ],
                m := 1,
                c := L!z12^3 - z12>,
            rec<SiegelPower | 
                a := [ 5/12, 5/6 ],
                m := 1,
                c := L!z24^3>,
            rec<SiegelPower | 
                a := [ 5/12, 7/12 ],
                m := 1,
                c := L!z24^3>,
            rec<SiegelPower | 
                a := [ 1/12, 1/6 ],
                m := 1,
                c := L!-z24^5>,
            rec<SiegelPower | 
                a := [ 1/3, 11/12 ],
                m := 1,
                c := L!-z24^5>,
            rec<SiegelPower | 
                a := [ 1/3, 5/12 ],
                m := 1,
                c := L!z24^2>
        ];
    t4:=[
            rec<SiegelPower | 
                a := [ 5/12, 5/12 ],
                m := 1,
                c := L!1/2*(-z24^7 + z24^3)>,
            rec<SiegelPower | 
                a := [ 5/12, 0 ],
                m := 1,
                c := L!-z24^5>,
            rec<SiegelPower | 
                a := [ 1/12, 3/4 ],
                m := 1,
                c := L!-1>,
            rec<SiegelPower | 
                a := [ 1/12, 1/3 ],
                m := 1,
                c := L!-z24^7 + z24^3>,
            rec<SiegelPower | 
                a := [ 1/6, 1/4 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 1/6, 11/12 ],
                m := 1,
                c := L!-1>,
            rec<SiegelPower | 
                a := [ 1/6, 3/4 ],
                m := 1,
                c := L!z24^7>,
            rec<SiegelPower | 
                a := [ 1/6, 5/12 ],
                m := 1,
                c := L!-z24^5>,
            rec<SiegelPower | 
                a := [ 1/12, 0 ],
                m := 1,
                c := L!1>,
            rec<SiegelPower | 
                a := [ 5/12, 3/4 ],
                m := 1,
                c := L!z24^5>,
            rec<SiegelPower | 
                a := [ 5/12, 2/3 ],
                m := 1,
                c := L!z24^2>,
            rec<SiegelPower | 
                a := [ 1/12, 1/12 ],
                m := 1,
                c := L!-z24^5>
        ];
    t5:=[
            rec<SiegelPower | 
                a := [ 5/12, 5/12 ],
                m := 0,
                c := L!z24^6 - z24^4 - z24^2>
        ];
        
        
    t := [t0,t1,t2,t3,t4,t5];

    Gamma`hauptmodul := t;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    h1 := Gamma`hauptmodul; 
    
    Gamma`h := R!SiegelExpansion(h1,10); 
    CPlist[k] :=Gamma;
    
    
    end if;
    
    
    
end for;

// Normalizing the q expansions of hauptmoduls
for k in Keys(CPlist) do
    if k eq "1A" then
        continue;
    end if;
    Gamma:=CPlist[k];
    N:=Gamma`N;
    R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
    a := LeadingCoefficient(Gamma`h);
    b := Coefficient(Gamma`h,0);
    if a eq 1 and b eq 0 then
        continue k;
    end if;
    

    t := Gamma`hauptmodul; 
    
   
    
    if Type(t[1]) eq SeqEnum then
        
        for p in t do
            w := (p[1]`c)/a;
            x :=p[1];
            x`c := w;
            
        end for;
        Gamma`hauptmodul :=t;
        t1 := [rec<SiegelPower | a := [ 0, 1/N ],m := 0,c := -b/a>];
        Gamma`hauptmodul := Append(Gamma`hauptmodul,t1);
        Gamma`h := R!SiegelExpansion(Gamma`hauptmodul,10); 
        CPlist[k] :=Gamma;

    else
        t[1]`c := (t[1]`c)/(a);
        t1 := [rec<SiegelPower | a := [ 0, 1/N ],m := 0,c := -b/a>];
        Gamma`hauptmodul := [t,t1];
        Gamma`h := R!SiegelExpansion(Gamma`hauptmodul,10); 
        CPlist[k] :=Gamma;
    end if;
    
end for;

L<z96>:=CyclotomicField(96);
K<z16>:=CyclotomicField(16);
Gamma := CPlist["16A"];
 N:=Gamma`N;
 R<q>:=PuiseuxSeriesRing(CyclotomicField(N)); 
Gamma`hauptmodul :=[
    [
        rec<SiegelPower | 
            a := [ 1/4, 0 ],
            m := 1,
            c := L!-z96^15>,
        rec<SiegelPower | 
            a := [ 1/4, 1/4 ],
            m := 1,
            c := L!1>,
        rec<SiegelPower | 
            a := [ 1/2, 1/4 ],
            m := 1,
            c := L!1>
    ],
    [
        rec<SiegelPower | 
            a := [ 0, 1/4 ],
            m := 1,
            c := L!-z96^23 + z96^7>,
        rec<SiegelPower | 
            a := [ 1/4, 3/4 ],
            m := 1,
            c := L!z12^3>,
        rec<SiegelPower | 
            a := [ 1/4, 1/2 ],
            m := 1,
            c := L!z24^6>
    ],
    [
        rec<SiegelPower | 
            a := [ 0, 1/16 ],
            m := 0,
            c := L!0>
    ]
];
Gamma`h := R!SiegelExpansion(Gamma`hauptmodul,10); 
CPlist["16A"] :=Gamma;


// For a congruence subgroup Gamma, determines the congruence subgroups Gamma' in the list that contain, and do not equal, Gamma.   
// We then order them by decreasing index in SL(2,Z).

for k  in Keys(CPlist) do
    Gamma:=CPlist[k]; 
    if Gamma`label eq "1A" then
       CPlist[k]`sup:=[]; continue k;
    end if; 
    N:=Gamma`N; H:=Gamma`H; 
    SL2:=SL(2,Integers(N));   

    Gamma`sup:=["1A"];
    for k_ in Keys(CPlist) do
        if k_ eq "1A" then continue k_; end if;
        if k_ eq k then continue k_; end if;
 
        Gamma_:=CPlist[k_];
        N_:=Gamma_`N; H_:=Gamma_`H;

        if N mod N_ eq 0 then
           SL2_:=SL(2,Integers(N_));
           red:=hom<SL2->SL2_|[SL2_!SL2.i: i in [1..#Generators(SL2)]]>;
           if H subset (H_ @@ red) then
              Gamma`sup:=Gamma`sup cat [Gamma_`label];
           end if;
        end if;
    end for;
    CPlist[k]:=Gamma;
end for;

for k in Keys(CPlist) do
    sup:=CPlist[k]`sup; 
    ind:=[CPlist[k_]`index: k_ in sup];
    ParallelSort(~ind, ~sup); 
    Reverse(~sup);
    CPlist[k]`sup:=sup;
end for;


// For the computed hauptmodul h of X_Gamma, computes the rational function J
// such that J(h) is the modular j-invariant. 


// The case "24B" is coded separetely because Magma on the systems was slow when I computed it. I computed it on Magma calculator and then entered it here.
keys:=[k: k in Keys(CPlist)];
ind:=[CPlist[k]`index:k in keys];
ParallelSort(~ind, ~keys);

for k in keys do
    
    Gamma:=CPlist[k];  N:=Gamma`N;
    F<t>:=FunctionField(CyclotomicField(N));
    if k eq "1A" then
       CPlist[k]`J:=t; CPlist[k]`h:=jInvariant(q);continue k; 
       
    end if;
    if k eq "24B" then
       CPlist[k]`J:=(t^48 - 36*t^44 + 1242*t^40 - 24084*t^36 + 407511*t^32 - 4671432*t^28 + 

    42908940*t^24 - 265011912*t^20 + 977319999*t^16 - 2085374484*t^12 + 

    2496709818*t^8 - 1549681956*t^4 + 387420489)/(t^40 - 28*t^36 + 270*t^32 - 

    972*t^28 + 729*t^24) ;continue k;
    
    end if; 
    Gamma_:=CPlist[ Gamma`sup[1] ];
    
    f:=F!FindRelation(Gamma`h,Gamma_`h, Gamma`index div Gamma_`index);

    CPlist[k]`J:=Evaluate(F!Gamma_`J, f);
    
end for;




