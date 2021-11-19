gap> START_TEST("TensorInducedMatrixGroups.tst");

#
gap> TestTensorInducedDecompositionStabilizerInSL := function(args)
>   local m, t, q, G, hasSize;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSL(m, t, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSL([3, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSL([2, 2, 7]);
gap> TestTensorInducedDecompositionStabilizerInSL([2, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSL([3, 3, 3]);

#
gap> TestTensorInducedDecompositionStabilizerInSU := function(args)
>   local m, t, q, G, hasSize;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   hasSize := HasSize(G);
>   Assert(0, IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSU([2, 2, 7]);
gap> TestTensorInducedDecompositionStabilizerInSU([2, 2, 5]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 2, 3]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 3, 3]);
gap> TestTensorInducedDecompositionStabilizerInSU([3, 2, 5]);

#
gap> STOP_TEST("TensorInducedMatrixGroups.tst", 0);
