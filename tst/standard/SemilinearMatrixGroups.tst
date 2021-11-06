gap> TestGammaLMeetSL := function(args)
>   local n, q, s, G, hasSize;
>   n := args[1];
>   q := args[2];
>   s := args[3];
>   G := GammaLMeetSL(n, q, s);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q)
>          and hasSize;
> end;;
gap> testsGammaLMeetSL := [[4, 3, 2], [2, 2, 2], [6, 5, 3], [3, 4, 3]];;
gap> ForAll(testsGammaLMeetSL, TestGammaLMeetSL);
true
gap> TestGammaLMeetSU := function(args)
>   local n, q, s, G, hasSize;
>   n := args[1];
>   q := args[2];
>   s := args[3];
>   G := GammaLMeetSU(n, q, s);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2)
>          and hasSize;
> end;;
gap> testsGammaLMeetSU := [[3, 5, 3], [6, 3, 3], [3, 7, 3]];;
gap> ForAll(testsGammaLMeetSU, TestGammaLMeetSU);
true
gap> TestSymplecticSemilinearSp := function(args)
>   local n, q, s, G, hasSize;
>   n := args[1];
>   q := args[2];
>   s := args[3];
>   G := SymplecticSemilinearSp(n, q, s);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(Sp(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q)
>          and hasSize;
> end;;
gap> testsSymplecticSemilinearSp := [[4, 7, 2], [6, 5, 3], [8, 4, 2]];;
gap> ForAll(testsSymplecticSemilinearSp, TestSymplecticSemilinearSp);
true
gap> TestUnitarySemilinearSp := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := UnitarySemilinearSp(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(Sp(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q)
>          and hasSize;
> end;;
gap> testsUnitarySemilinearSp := [[4, 7], [8, 5], [4, 5]];;
gap> ForAll(testsUnitarySemilinearSp, TestUnitarySemilinearSp);
true
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ := function(args)
>   local q, s, gens;
>   q := args[1];
>   s := args[2];
>   gens := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
>   return Order(gens.A) = (q ^ s - 1) and Order(gens.B) = s;
> end;;
gap> testsMatricesInducingGaloisGroupOfGFQToSOverGFQ := [[3, 2], [2, 2], [5, 3], [4, 3]];;
gap> ForAll(testsMatricesInducingGaloisGroupOfGFQToSOverGFQ, TestMatricesInducingGaloisGroupOfGFQToSOverGFQ);
true
