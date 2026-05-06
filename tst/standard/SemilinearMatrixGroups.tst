gap> START_TEST("SemilinearMatrixGroups.tst");

#
gap> TestGammaLMeetSL := function(n, q, s)
>   local G;
>   G := GammaLMeetSL(n, q, s);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestGammaLMeetSL(4, 3, 2);
gap> TestGammaLMeetSL(2, 2, 2);
gap> TestGammaLMeetSL(6, 5, 3);
gap> TestGammaLMeetSL(3, 4, 3);

#
gap> TestGammaLMeetSU := function(n, q, s)
>   local G;
>   G := GammaLMeetSU(n, q, s);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestGammaLMeetSU(3, 5, 3);
gap> TestGammaLMeetSU(6, 3, 3);
gap> TestGammaLMeetSU(3, 7, 3);

#
gap> TestSymplecticSemilinearSp := function(n, q, s)
>   local G;
>   G := SymplecticSemilinearSp(n, q, s);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSymplecticSemilinearSp(4, 7, 2);
gap> TestSymplecticSemilinearSp(6, 5, 3);
gap> TestSymplecticSemilinearSp(8, 4, 2);

#
gap> TestUnitarySemilinearSp := function(n, q)
>   local G;
>   G := UnitarySemilinearSp(n, q);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
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
gap> TestGammaLMeetOmega := function(epsilon, d, q, s)
>   local G;
>   G := GammaLMeetOmega(epsilon, d, q, s);
>   CheckIsSubsetOmega(epsilon, d, q, G);
>   CheckSize(G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestGammaLMeetOmega(0, 9, 7, 3);  # FIXME: `Error, Could not find hash function for sample object` (recog issue #123)
#@fi
gap> TestGammaLMeetOmega(0, 15, 3, 3);
gap> TestGammaLMeetOmega(0, 15, 3, 5);
gap> TestGammaLMeetOmega(1, 12, 3, 3);
gap> TestGammaLMeetOmega(1, 12, 5, 3);
gap> TestGammaLMeetOmega(1, 20, 3, 5);
gap> TestGammaLMeetOmega(-1, 12, 3, 3);
gap> TestGammaLMeetOmega(-1, 12, 5, 3);

#
gap> TestUnitarySemilinearOmega := function(d, q)
>   local G;
>   G := UnitarySemilinearOmega(d, q);
>   CheckIsSubsetOmega((-1) ^ (d / 2), d, q, G);
>   CheckSize(G);
> end;;
gap> TestUnitarySemilinearOmega(4, 5);
gap> TestUnitarySemilinearOmega(4, 4);
gap> TestUnitarySemilinearOmega(4, 7);
gap> TestUnitarySemilinearOmega(6, 3);
gap> TestUnitarySemilinearOmega(6, 4);
gap> TestUnitarySemilinearOmega(6, 5);
gap> TestUnitarySemilinearOmega(6, 8);

#
gap> TestOrthogonalSemilinearOmega := function(epsilon, epsilon1, d, q)
>   local G;
>   G := OrthogonalSemilinearOmega(epsilon, epsilon1, d, q);
>   CheckIsSubsetOmega(epsilon, d, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalSemilinearOmega(1, 0, 6, 3);
gap> TestOrthogonalSemilinearOmega(-1, 0, 6, 3);
gap> TestOrthogonalSemilinearOmega(1, 0, 6, 5);
gap> TestOrthogonalSemilinearOmega(-1, 0, 6, 5);
gap> TestOrthogonalSemilinearOmega(1, 1, 8, 7);
gap> TestOrthogonalSemilinearOmega(-1, -1, 8, 7);
gap> TestOrthogonalSemilinearOmega(1, 1, 8, 5);
gap> TestOrthogonalSemilinearOmega(-1, -1, 8, 5);

#
gap> STOP_TEST("SemilinearMatrixGroups.tst", 0);
