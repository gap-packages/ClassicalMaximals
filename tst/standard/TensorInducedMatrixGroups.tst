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
>   return IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q)
>          and hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsTensorInducedDecompositionStabilizerInSL := [[3, 2, 5], [2, 2, 7], [2, 2, 5], [3, 3, 3]];;
#@else
gap> testsTensorInducedDecompositionStabilizerInSL := [[3, 2, 5], [2, 2, 7], [3, 3, 3]];;
#@fi
gap> ForAll(testsTensorInducedDecompositionStabilizerInSL, TestTensorInducedDecompositionStabilizerInSL);
true
gap> TestTensorInducedDecompositionStabilizerInSU := function(args)
>   local m, t, q, G, hasSize;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   hasSize := HasSize(G);
>   return IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2)
>          and hasSize;
> end;;
gap> testsTensorInducedDecompositionStabilizerInSU := [[2, 2, 7], [2, 2, 5], [3, 2, 3], [3, 3, 3], [3, 2, 5]];;
gap> ForAll(testsTensorInducedDecompositionStabilizerInSU, TestTensorInducedDecompositionStabilizerInSU);
true

#
gap> STOP_TEST("TensorInducedMatrixGroups.tst", 0);
