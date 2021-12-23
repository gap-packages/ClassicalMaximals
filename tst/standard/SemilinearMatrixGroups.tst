gap> START_TEST("SemilinearMatrixGroups.tst");

#
gap> TestGammaLMeetSL := function(n, q, s)
>   local G;
>   G := GammaLMeetSL(n, q, s);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSL(n, q, G));
> end;;
gap> TestGammaLMeetSL(4, 3, 2);
gap> TestGammaLMeetSL(2, 2, 2);
gap> TestGammaLMeetSL(6, 5, 3);
gap> TestGammaLMeetSL(3, 4, 3);

#
gap> TestGammaLMeetSU := function(n, q, s)
>   local G;
>   G := GammaLMeetSU(n, q, s);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSU(n, q, G));
> end;;
gap> TestGammaLMeetSU(3, 5, 3);
gap> TestGammaLMeetSU(6, 3, 3);
gap> TestGammaLMeetSU(3, 7, 3);

#
gap> TestSymplecticSemilinearSp := function(n, q, s)
>   local G;
>   G := SymplecticSemilinearSp(n, q, s);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
> end;;
gap> TestSymplecticSemilinearSp(4, 7, 2);
gap> TestSymplecticSemilinearSp(6, 5, 3);
gap> TestSymplecticSemilinearSp(8, 4, 2);

#
gap> TestUnitarySemilinearSp := function(n, q)
>   local G;
>   G := UnitarySemilinearSp(n, q);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
> end;;
gap> TestUnitarySemilinearSp(4, 7);
gap> TestUnitarySemilinearSp(8, 5);
gap> TestUnitarySemilinearSp(6, 5);

#
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ := function(q, s)
>   local gens;
>   gens := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
>   Assert(0, Order(gens.A) = (q ^ s - 1));
>   Assert(0, Order(gens.B) = s);
> end;;
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ(3, 2);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ(2, 2);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ(5, 3);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ(4, 3);

#
gap> STOP_TEST("SemilinearMatrixGroups.tst", 0);
