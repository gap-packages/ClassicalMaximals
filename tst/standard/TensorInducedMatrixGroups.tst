gap> START_TEST("TensorInducedMatrixGroups.tst");

#
gap> TestTensorInducedDecompositionStabilizerInSL := function(args)
>   local m, t, q, G;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSL(m, t, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSL(m ^ t, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestTensorInducedDecompositionStabilizerInSL([3, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSL([2, 2, 7]);
gap> TestTensorInducedDecompositionStabilizerInSL([2, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSL([3, 3, 3]);

#
gap> TestTensorInducedDecompositionStabilizerInSU := function(args)
>   local m, t, q, G;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   Assert(0, IsSubsetSU(m ^ t, q, G));
>   Assert(0, HasSize(G));
> end;;
gap> TestTensorInducedDecompositionStabilizerInSU([2, 2, 7]);
gap> TestTensorInducedDecompositionStabilizerInSU([2, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 2, 3]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 3, 3]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 2, 5]);

#
gap> TestTensorInducedDecompositionStabilizerInSp := function(args)
>   local m, t, q, G;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSp(m, t, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSp(m ^ t, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestTensorInducedDecompositionStabilizerInSp([2, 3, 7]);
gap> TestTensorInducedDecompositionStabilizerInSp([4, 3, 3]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorInducedDecompositionStabilizerInSp([2, 5, 3]); # FIXME: see https://github.com/gap-packages/recog/issues/302
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
