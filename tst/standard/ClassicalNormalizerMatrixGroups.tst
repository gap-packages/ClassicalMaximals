gap> START_TEST("ClassicalNormalizerMatrixGroups.tst");

#
gap> TestSymplecticNormalizerInSL := function(n, q)
>   local G;
>   G := SymplecticNormalizerInSL(n, q);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSymplecticNormalizerInSL(4, 3);
gap> TestSymplecticNormalizerInSL(4, 5);
gap> TestSymplecticNormalizerInSL(6, 4);

#
gap> TestUnitaryNormalizerInSL := function(n, q)
>   local G;
>   G := UnitaryNormalizerInSL(n, q);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestUnitaryNormalizerInSL(4, 9);
gap> TestUnitaryNormalizerInSL(3, 9);
gap> TestUnitaryNormalizerInSL(4, 4);

#
gap> TestOrthogonalNormalizerInSL := function(epsilon, n, q)
>   local G;
>   G := OrthogonalNormalizerInSL(epsilon, n, q);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalNormalizerInSL(0, 3, 5);
gap> TestOrthogonalNormalizerInSL(-1, 6, 5);
gap> TestOrthogonalNormalizerInSL(1, 6, 5);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOrthogonalNormalizerInSL(-1, 4, 3); # FIXME: see https://github.com/gap-packages/recog/issues/313
#@fi
gap> TestOrthogonalNormalizerInSL(1, 4, 3);
gap> TestOrthogonalNormalizerInSL(-1, 4, 5);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOrthogonalNormalizerInSL(1, 4, 5); # FIXME: see https://github.com/gap-packages/recog/issues/316
#@fi
gap> TestOrthogonalNormalizerInSL(-1, 6, 3);

#
gap> TestOrthogonalInSp := function(epsilon, n, q)
>   local G;
>   G := OrthogonalInSp(epsilon, n, q);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOrthogonalInSp(1, 4, 8);
gap> TestOrthogonalInSp(-1, 6, 2);
#@fi
gap> TestOrthogonalInSp(-1, 4, 4);
gap> TestOrthogonalInSp(1, 6, 2);

#
gap> STOP_TEST("ClassicalNormalizerMatrixGroups.tst", 0);
