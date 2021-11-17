gap> START_TEST("SemilinearMatrixGroups.tst");

#
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

#
gap> STOP_TEST("SemilinearMatrixGroups.tst", 0);
