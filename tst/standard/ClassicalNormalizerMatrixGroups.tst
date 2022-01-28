gap> START_TEST("ClassicalNormalizerMatrixGroups.tst");

#
gap> TestSymplecticNormalizerInSL := function(n, q)
>   local G;
>   G := SymplecticNormalizerInSL(n, q);
>   CheckSize(G);
>   CheckIsSubsetSL(n, q, G);
> end;;
gap> TestSymplecticNormalizerInSL(4, 3);
gap> TestSymplecticNormalizerInSL(4, 5);
gap> TestSymplecticNormalizerInSL(6, 4);

#
gap> TestUnitaryNormalizerInSL := function(n, q)
>   local G;
>   G := UnitaryNormalizerInSL(n, q);
>   CheckSize(G);
>   CheckIsSubsetSL(n, q, G);
> end;;
gap> TestUnitaryNormalizerInSL(4, 9);
gap> TestUnitaryNormalizerInSL(3, 9);
gap> TestUnitaryNormalizerInSL(4, 4);

#
gap> TestOrthogonalNormalizerInSL := function(epsilon, n, q)
>   local G;
>   G := OrthogonalNormalizerInSL(epsilon, n, q);
>   CheckSize(G);
>   CheckIsSubsetSL(n, q, G);
> end;;
gap> TestOrthogonalNormalizerInSL(0, 3, 5);
gap> TestOrthogonalNormalizerInSL(-1, 6, 5);
gap> TestOrthogonalNormalizerInSL(1, 6, 5);
gap> TestOrthogonalNormalizerInSL(-1, 4, 3);
gap> TestOrthogonalNormalizerInSL(1, 4, 3);
gap> TestOrthogonalNormalizerInSL(-1, 4, 5);
gap> TestOrthogonalNormalizerInSL(1, 4, 5);
gap> TestOrthogonalNormalizerInSL(-1, 6, 3);

#
gap> TestOrthogonalInSp := function(epsilon, n, q)
>   local G;
>   G := OrthogonalInSp(epsilon, n, q);
>   CheckSize(G);
>   CheckIsSubsetSp(n, q, G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOrthogonalInSp(1, 4, 8);
gap> TestOrthogonalInSp(-1, 6, 2);
#@fi
gap> TestOrthogonalInSp(-1, 4, 4);
gap> TestOrthogonalInSp(1, 6, 2);

#
gap> STOP_TEST("ClassicalNormalizerMatrixGroups.tst", 0);
