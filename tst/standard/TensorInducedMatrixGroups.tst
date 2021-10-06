gap> TestTensorInducedDecompositionStabilizerInSL := function(args)
>   local m, t, q, G;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSL(m, t, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsTensorInducedDecompositionStabilizerInSL := [[3, 2, 5], [2, 2, 7], [2, 2, 5], [3, 3, 3]];;
gap> ForAll(testsTensorInducedDecompositionStabilizerInSL, TestTensorInducedDecompositionStabilizerInSL);
true
gap> TestTensorInducedDecompositionStabilizerInSU := function(args)
>   local m, t, q, G;
>   m := args[1];
>   t := args[2];
>   q := args[3];
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
gap> testsTensorInducedDecompositionStabilizerInSU := [[2, 2, 7], [2, 2, 5], [3, 2, 3], [3, 3, 3], [3, 2, 5]];;
gap> ForAll(testsTensorInducedDecompositionStabilizerInSU, TestTensorInducedDecompositionStabilizerInSU);
true
