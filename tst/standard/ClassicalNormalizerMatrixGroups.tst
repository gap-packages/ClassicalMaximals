gap> START_TEST("ClassicalNormalizerMatrixGroups.tst");

#
gap> TestSymplecticNormalizerInSL := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := SymplecticNormalizerInSL(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestSymplecticNormalizerInSL([4, 3]);
gap> TestSymplecticNormalizerInSL([4, 5]);
gap> TestSymplecticNormalizerInSL([6, 4]);

#
gap> TestUnitaryNormalizerInSL := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := UnitaryNormalizerInSL(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestUnitaryNormalizerInSL([4, 9]);
gap> TestUnitaryNormalizerInSL([3, 9]);
gap> TestUnitaryNormalizerInSL([4, 4]);

#
gap> TestOrthogonalNormalizerInSL := function(args)
>   local epsilon, n, q, G, hasSize;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   G := OrthogonalNormalizerInSL(epsilon, n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestOrthogonalNormalizerInSL([0, 3, 5]);
gap> TestOrthogonalNormalizerInSL([-1, 6, 5]);
gap> TestOrthogonalNormalizerInSL([1, 6, 5]);
gap> TestOrthogonalNormalizerInSL([-1, 4, 3]);
gap> TestOrthogonalNormalizerInSL([1, 4, 3]);
gap> TestOrthogonalNormalizerInSL([-1, 4, 5]);
gap> TestOrthogonalNormalizerInSL([1, 4, 5]);
gap> TestOrthogonalNormalizerInSL([-1, 6, 3]);

#
gap> TestOrthogonalInSp := function(args)
>   local epsilon, n, q, G, hasSize;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   G := OrthogonalInSp(epsilon, n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOrthogonalInSp([1, 4, 8]);
gap> TestOrthogonalInSp([-1, 6, 2]);
#@fi
gap> TestOrthogonalInSp([-1, 4, 4]);
gap> TestOrthogonalInSp([1, 6, 2]);

#
gap> STOP_TEST("ClassicalNormalizerMatrixGroups.tst", 0);
