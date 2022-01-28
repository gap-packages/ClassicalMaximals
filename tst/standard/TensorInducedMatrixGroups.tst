gap> START_TEST("TensorInducedMatrixGroups.tst");

#
gap> TestTensorInducedDecompositionStabilizerInSL := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSL(m, t, q);
>   CheckSize(G);
>   CheckIsSubsetSL(m ^ t, q, G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSL(3, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSL(2, 2, 7);
gap> TestTensorInducedDecompositionStabilizerInSL(2, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSL(3, 3, 3);

#
gap> TestTensorInducedDecompositionStabilizerInSU := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   CheckIsSubsetSU(m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSU(2, 2, 7);
gap> TestTensorInducedDecompositionStabilizerInSU(2, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 2, 3);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 3, 3);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 2, 5);

#
gap> TestTensorInducedDecompositionStabilizerInSp := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSp(m, t, q);
>   CheckSize(G);
>   CheckIsSubsetSp(m ^ t, q, G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSp(2, 3, 7);
gap> TestTensorInducedDecompositionStabilizerInSp(4, 3, 3);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorInducedDecompositionStabilizerInSp(2, 5, 3); # FIXME: see https://github.com/gap-packages/recog/issues/302
#@fi

# Test error handling
gap> TensorInducedDecompositionStabilizerInSp(3, 3, 3);
Error, <m> must be even
gap> TensorInducedDecompositionStabilizerInSp(2, 2, 5);
Error, <t> must be odd
gap> TensorInducedDecompositionStabilizerInSp(2, 3, 4);
Error, <q> must be odd

#
gap> STOP_TEST("TensorInducedMatrixGroups.tst", 0);
