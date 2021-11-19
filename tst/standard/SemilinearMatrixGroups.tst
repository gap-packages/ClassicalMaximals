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
>   Assert(0, IsSubset(SL(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestGammaLMeetSL([4, 3, 2]);
gap> TestGammaLMeetSL([2, 2, 2]);
gap> TestGammaLMeetSL([6, 5, 3]);
gap> TestGammaLMeetSL([3, 4, 3]);

#
gap> TestGammaLMeetSU := function(args)
>   local n, q, s, G, hasSize;
>   n := args[1];
>   q := args[2];
>   s := args[3];
>   G := GammaLMeetSU(n, q, s);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestGammaLMeetSU([3, 5, 3]);
gap> TestGammaLMeetSU([6, 3, 3]);
gap> TestGammaLMeetSU([3, 7, 3]);

#
gap> TestSymplecticSemilinearSp := function(args)
>   local n, q, s, G, hasSize;
>   n := args[1];
>   q := args[2];
>   s := args[3];
>   G := SymplecticSemilinearSp(n, q, s);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestSymplecticSemilinearSp([4, 7, 2]);
gap> TestSymplecticSemilinearSp([6, 5, 3]);
gap> TestSymplecticSemilinearSp([8, 4, 2]);

#
gap> TestUnitarySemilinearSp := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := UnitarySemilinearSp(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestUnitarySemilinearSp([4, 7]);
gap> TestUnitarySemilinearSp([8, 5]);
gap> TestUnitarySemilinearSp([6, 5]);

#
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ := function(args)
>   local q, s, gens;
>   q := args[1];
>   s := args[2];
>   gens := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
>   Assert(0, Order(gens.A) = (q ^ s - 1));
>   Assert(0, Order(gens.B) = s);
> end;;
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ([3, 2]);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ([2, 2]);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ([5, 3]);
gap> TestMatricesInducingGaloisGroupOfGFQToSOverGFQ([4, 3]);

#
gap> STOP_TEST("SemilinearMatrixGroups.tst", 0);
