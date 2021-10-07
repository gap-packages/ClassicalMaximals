gap> TestTensorProductStabilizerInSL := function(args)
>   local d1, d2, q, G, hasSize;
>   d1 := args[1];
>   d2 := args[2];
>   q := args[3];
>   G := TensorProductStabilizerInSL(d1, d2, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(d1 * d2, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q)
>          and hasSize;
> end;;
gap> testsTensorProductStabilizerInSL := [[2, 3, 2], [2, 3, 3], [2, 3, 4], [2, 3, 5], [2, 4, 3], [3, 4, 2], [3, 4, 3]];;
gap> ForAll(testsTensorProductStabilizerInSL, TestTensorProductStabilizerInSL);
true
gap> TestTensorProductStabilizerInSU := function(args)
>   local d1, d2, q, G, hasSize;
>   d1 := args[1];
>   d2 := args[2];
>   q := args[3];
>   G := TensorProductStabilizerInSU(d1, d2, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(d1 * d2, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2)
>          and hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsTensorProductStabilizerInSU := [[2, 3, 2], [2, 3, 3], [2, 3, 4], [2, 4, 3]];;
#@else
gap> testsTensorProductStabilizerInSU := [[2, 3, 2], [2, 3, 3]];;
#@fi
gap> ForAll(testsTensorProductStabilizerInSU, TestTensorProductStabilizerInSU);
true
